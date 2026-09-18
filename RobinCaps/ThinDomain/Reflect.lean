import RobinCaps.Sobolev.RadialSlice
import RobinCaps.ThinDomain.SphereSlicing

/-!
# Even reflection of the hemispherical cap and the trace on its curved boundary

This file transports the radial-slice trace machinery of `RobinCaps/Sobolev/RadialSlice.lean`
(which lives on a **full** Euclidean ball) to the **hemispherical end cap**
`(Cap.hemisphere m).body ⊆ CapSpace m = ℝ × EuclideanSpace ℝ (Fin m)`, by **even reflection**
across the flat entrance face.

## Conventions

The hemispherical cap has `K = 1` and profile `θ s = √(1 - (s+1)²)`, so

`(Cap.hemisphere m).body = {(s,z) | -1 < s < 0 ∧ ‖z‖ < √(1-(s+1)²)}`,

i.e. after the **recentring** `t = s + 1` it is the *open half ball*
`{(t,z) | t² + ‖z‖² < 1 ∧ 0 < t}` of the unit ball of `ℝ^{m+1}` centred at the entrance centre.
The entrance (flat) face is `s = -1` (`t = 0`) and the curved boundary `Γ` is the half sphere
`{x | ‖x‖ = 1 ∧ 0 < x 0}`.  This is exactly the convention of
`RobinCaps.ThinDomain.capSphereFun`, which reads the boundary point of direction `w` off as
`(w 0 - 1, w')`.  In particular the relevant half sphere is `{w | 0 < w 0}` (**not** `w 0 < 0`).

## Contents

* `toBall`, `toBallNeg`, `ofBall`, `ofBallNeg`, `capPt`: the recentring `(s,z) ↦ (s+1,z)`, its
  reflected companion `(s,z) ↦ (-(s+1),z)`, their inverses and the *folding* map
  `x ↦ (|x 0| - 1, x')` which sends a point of the ball to the point of the cap body over it.
  They are measure preserving (`measurePreserving_toBall`, `measurePreserving_toBallNeg`) and
  identify the cap body with the two open half balls (`toBall_preimage_upper`,
  `toBallNeg_preimage_lower`).
* `memLp_ball_of_halves_rf`, `setIntegral_ball_of_halves_rf`: the gluing lemmas expressing an
  `L²` function / an integral on the ball through the two halves.
* `faceCut ε`, the smooth axial cut-off vanishing for `s + 1 ≤ ε`, with `tendsto_mul_faceCut`
  (dominated convergence) and `tendsto_faceCut_error` (the error term produced by
  differentiating the cut-off tends to zero, using that a test function vanishing on the
  entrance face is `O(s+1)` there, by the Lipschitz bound of
  `ContDiff.lipschitzWith_of_hasCompactSupport`).
* `weakGrad_transverse_face` and `weakGrad_axial_face`: **the two weak-derivative identities of
  `u` for test functions whose support reaches the entrance face**; in the axial direction the
  test function is required to vanish on the face.  These replace the axial ACL/`sliceAC`
  argument: no absolutely continuous representative is needed, only the cut-off.
* `reflectEven_hasWeakGrad` and `reflectEven` (**deliverable 1**): the even reflection
  `u(|t|-1,z)`, with the odd axial and even transverse reflected gradient, is an element of
  `RobinCaps.Sobolev.Weak.H1 (ball 0 1)` of `ℝ^{m+1}`.  The weak-gradient identity for a test
  function `φ` of the ball is obtained by splitting the ball into its two halves; the two halves
  produce the *odd* symmetrisation `φ ∘ toBall - φ ∘ toBallNeg` in the axial direction (which
  vanishes on the face) and the *even* one in the transverse directions.
  `mass_reflectEven`, `dirichlet_reflectEven`: both energies exactly double.
* `gammaTrace`, `gammaTrace_eq_of_continuous`, `gammaTrace_sq_integral_le`
  (**deliverable 2**): the trace on the curved boundary `Γ` is the sphere trace of the
  reflection at radius `1`, and
  `∫_{S^m} |Tr u|² dσ ≤ 2 · max (4·2^m) (2^m) · (massP u + dirichletP u)`.
* `gammaTraceFun`, `capSphereFun_gammaTraceFun`, `capLateralIntegral_gammaTrace_sq_le`
  (**deliverable 3**): the same bound for the project's surface-of-revolution integral
  `capLateralIntegral` of the cap, through `capLateralIntegral_hemisphere_eq`;
  `integrable_gammaTrace_sq_of_continuous` discharges its integrability hypothesis for a
  continuous representative.
* `traceSphere_add_rf`, `traceSphere_smul_rf`, `gammaTrace_add`, `gammaTrace_smul`
  (**deliverable 4**): linearity of the trace, a.e. for the sum (through the uniqueness of the
  constant in `traceSphere_eq_const_add`) and everywhere for scalars.

Everything is proved without `sorry`, `admit`, `axiom` or `native_decide`.
-/

open MeasureTheory Metric Set Filter

open scoped ContDiff ENNReal Topology

namespace RobinCaps.ThinDomain

open RobinCaps.Domain RobinCaps.Sobolev.Weak

noncomputable section

variable {m : ℕ}

/-! ## The recentred model of the hemispherical cap -/

/-- The recentring identification `(s,z) ↦ (s+1, z) ∈ ℝ^{m+1}`: it maps the body of the
hemispherical cap onto the open upper half of the unit ball. -/
def toBall (m : ℕ) (p : CapSpace m) : EuclideanSpace ℝ (Fin (m + 1)) :=
  toEuclid m (p.1 + 1, p.2)

/-- The reflected recentring `(s,z) ↦ (-(s+1), z)`, mapping the cap body onto the open *lower*
half of the unit ball. -/
def toBallNeg (m : ℕ) (p : CapSpace m) : EuclideanSpace ℝ (Fin (m + 1)) :=
  toEuclid m (-(p.1 + 1), p.2)

/-- The inverse of `toBall`. -/
def ofBall (m : ℕ) (x : EuclideanSpace ℝ (Fin (m + 1))) : CapSpace m :=
  (x 0 - 1, (ofEuclid m x).2)

/-- The **even reflection base point**: `capPt x` is the point of the (closed) cap body lying
over `x`, obtained by folding the `0`-th coordinate, `t ↦ |t|`. -/
def capPt (m : ℕ) (x : EuclideanSpace ℝ (Fin (m + 1))) : CapSpace m :=
  (|x 0| - 1, (ofEuclid m x).2)

@[simp] theorem toBall_apply_zero (p : CapSpace m) : toBall m p 0 = p.1 + 1 := rfl

@[simp] theorem toBall_apply_succ (p : CapSpace m) (i : Fin m) : toBall m p i.succ = p.2 i := rfl

@[simp] theorem toBallNeg_apply_zero (p : CapSpace m) : toBallNeg m p 0 = -(p.1 + 1) := rfl

@[simp] theorem toBallNeg_apply_succ (p : CapSpace m) (i : Fin m) :
    toBallNeg m p i.succ = p.2 i := rfl

theorem norm_toBall_sq (p : CapSpace m) : ‖toBall m p‖ ^ 2 = (p.1 + 1) ^ 2 + ‖p.2‖ ^ 2 :=
  norm_toEuclid_sq _

theorem norm_toBallNeg_sq (p : CapSpace m) : ‖toBallNeg m p‖ ^ 2 = (p.1 + 1) ^ 2 + ‖p.2‖ ^ 2 := by
  rw [toBallNeg, norm_toEuclid_sq]
  ring

@[simp] theorem ofBall_toBall (p : CapSpace m) : ofBall m (toBall m p) = p := by
  rw [ofBall, toBall, ofEuclid_toEuclid]
  simp

@[simp] theorem toBall_ofBall (x : EuclideanSpace ℝ (Fin (m + 1))) : toBall m (ofBall m x) = x := by
  have h : ((ofBall m x).1 + 1, (ofBall m x).2) = ofEuclid m x := by
    refine Prod.ext ?_ rfl
    show x 0 - 1 + 1 = x 0
    ring
  rw [toBall, h, toEuclid_ofEuclid]

theorem capPt_eq_ofBall {x : EuclideanSpace ℝ (Fin (m + 1))} (hx : 0 ≤ x 0) :
    capPt m x = ofBall m x := by
  rw [capPt, ofBall, abs_of_nonneg hx]

theorem capPt_toBall {p : CapSpace m} (hp : -1 ≤ p.1) : capPt m (toBall m p) = p := by
  have h0 : (0 : ℝ) ≤ toBall m p 0 := by rw [toBall_apply_zero]; linarith
  rw [capPt_eq_ofBall h0, ofBall_toBall]

theorem capPt_toBallNeg {p : CapSpace m} (hp : -1 ≤ p.1) : capPt m (toBallNeg m p) = p := by
  have h0 : |toBallNeg m p 0| = p.1 + 1 := by
    rw [toBallNeg_apply_zero, abs_neg, abs_of_nonneg (by linarith : (0:ℝ) ≤ p.1 + 1)]
  refine Prod.ext ?_ ?_
  · show |toBallNeg m p 0| - 1 = p.1
    rw [h0]; ring
  · show (ofEuclid m (toBallNeg m p)).2 = p.2
    refine PiLp.ext fun i => ?_
    rfl

/-! ## The cap body as a half ball -/

/-- The recentred cap body *without* the sign condition: the full unit ball of the recentred
model, `{(s,z) | (s+1)² + ‖z‖² < 1}`. -/
def capQ (m : ℕ) : Set (CapSpace m) := {p | (p.1 + 1) ^ 2 + ‖p.2‖ ^ 2 < 1}

/-- The open upper half of the unit ball of `ℝ^{m+1}`. -/
def upperHalfBall (m : ℕ) : Set (EuclideanSpace ℝ (Fin (m + 1))) :=
  {x | ‖x‖ < 1 ∧ 0 < x 0}

/-- The open lower half of the unit ball of `ℝ^{m+1}`. -/
def lowerHalfBall (m : ℕ) : Set (EuclideanSpace ℝ (Fin (m + 1))) :=
  {x | ‖x‖ < 1 ∧ x 0 < 0}

theorem norm_lt_one_iff_sq_rf {x : EuclideanSpace ℝ (Fin (m + 1))} : ‖x‖ < 1 ↔ ‖x‖ ^ 2 < 1 := by
  constructor <;> intro h <;> nlinarith [norm_nonneg x]

/-- **The hemispherical cap body in recentred coordinates**: after `t = s+1` it is the open
upper half of the unit ball. -/
theorem mem_hemisphere_body_iff {p : CapSpace m} :
    p ∈ (Cap.hemisphere m).body ↔ -1 < p.1 ∧ (p.1 + 1) ^ 2 + ‖p.2‖ ^ 2 < 1 := by
  have hθ : (Cap.hemisphere m).θ p.1 = Real.sqrt (1 - (p.1 + 1) ^ 2) := rfl
  have hK : -(Cap.hemisphere m).K = (-1 : ℝ) := rfl
  simp only [Cap.body, Set.mem_setOf_eq, hθ, hK]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_⟩
    have := (Real.lt_sqrt (norm_nonneg p.2)).1 h3
    linarith
  · rintro ⟨h1, h2⟩
    have hz : ‖p.2‖ ^ 2 < 1 - (p.1 + 1) ^ 2 := by linarith
    have hpos : (0 : ℝ) < p.1 + 1 := by linarith
    have h2' : (p.1 + 1) ^ 2 < 1 := by nlinarith [sq_nonneg ‖p.2‖]
    refine ⟨h1, by nlinarith, (Real.lt_sqrt (norm_nonneg p.2)).2 hz⟩

theorem toBall_preimage_ball :
    toBall m ⁻¹' (ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) = capQ m := by
  ext p
  simp only [Set.mem_preimage, mem_ball_zero_iff, capQ, Set.mem_setOf_eq, norm_lt_one_iff_sq_rf,
    norm_toBall_sq]

theorem toBallNeg_preimage_ball :
    toBallNeg m ⁻¹' (ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) = capQ m := by
  ext p
  simp only [Set.mem_preimage, mem_ball_zero_iff, capQ, Set.mem_setOf_eq, norm_lt_one_iff_sq_rf,
    norm_toBallNeg_sq]

theorem body_eq_capQ_inter : (Cap.hemisphere m).body = capQ m ∩ {p : CapSpace m | -1 < p.1} := by
  ext p
  simp only [mem_hemisphere_body_iff, capQ, Set.mem_inter_iff, Set.mem_setOf_eq]
  tauto

theorem toBall_preimage_upper : toBall m ⁻¹' (upperHalfBall m) = (Cap.hemisphere m).body := by
  ext p
  simp only [Set.mem_preimage, upperHalfBall, Set.mem_setOf_eq, norm_lt_one_iff_sq_rf,
    norm_toBall_sq, toBall_apply_zero, mem_hemisphere_body_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨h2, by linarith⟩

theorem toBallNeg_preimage_lower : toBallNeg m ⁻¹' (lowerHalfBall m) = (Cap.hemisphere m).body := by
  ext p
  simp only [Set.mem_preimage, lowerHalfBall, Set.mem_setOf_eq, norm_lt_one_iff_sq_rf,
    norm_toBallNeg_sq, toBallNeg_apply_zero, mem_hemisphere_body_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨h2, by linarith⟩

theorem isOpen_body_rf : IsOpen ((Cap.hemisphere m).body) := by
  have h1 : Continuous fun p : CapSpace m => (p.1 + 1) ^ 2 + ‖p.2‖ ^ 2 :=
    ((continuous_fst.add continuous_const).pow 2).add (continuous_snd.norm.pow 2)
  have : (Cap.hemisphere m).body
      = {p : CapSpace m | (p.1 + 1) ^ 2 + ‖p.2‖ ^ 2 < 1} ∩ {p : CapSpace m | -1 < p.1} := by
    rw [body_eq_capQ_inter]; rfl
  rw [this]
  exact (isOpen_lt h1 continuous_const).inter (isOpen_lt continuous_const continuous_fst)

theorem measurableSet_body_rf : MeasurableSet ((Cap.hemisphere m).body) :=
  isOpen_body_rf.measurableSet

theorem continuous_coord_zero_rf :
    Continuous fun x : EuclideanSpace ℝ (Fin (m + 1)) => x 0 :=
  (EuclideanSpace.proj (0 : Fin (m + 1)) : EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] ℝ).continuous

theorem isOpen_upperHalfBall : IsOpen (upperHalfBall m) := by
  have h : upperHalfBall m
      = {x : EuclideanSpace ℝ (Fin (m + 1)) | ‖x‖ < 1} ∩ {x | 0 < x 0} := rfl
  rw [h]
  exact (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt continuous_const continuous_coord_zero_rf)

theorem isOpen_lowerHalfBall : IsOpen (lowerHalfBall m) := by
  have h : lowerHalfBall m
      = {x : EuclideanSpace ℝ (Fin (m + 1)) | ‖x‖ < 1} ∩ {x | x 0 < 0} := rfl
  rw [h]
  exact (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt continuous_coord_zero_rf continuous_const)

theorem measurableSet_upperHalfBall : MeasurableSet (upperHalfBall m) :=
  isOpen_upperHalfBall.measurableSet

theorem measurableSet_lowerHalfBall : MeasurableSet (lowerHalfBall m) :=
  isOpen_lowerHalfBall.measurableSet

/-! ## The two recentrings are measure preserving -/

theorem toEuclid_add_rf (p q : CapSpace m) :
    toEuclid m (p + q) = toEuclid m p + toEuclid m q := by
  refine PiLp.ext fun j => ?_
  refine Fin.cases ?_ (fun i => ?_) j
  · simp
  · simp

theorem toBall_eq_add (p : CapSpace m) : toBall m p = toEuclid m p + axis m := by
  have hp : ((p.1 + 1 : ℝ), p.2) = p + ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))) := by
    refine Prod.ext rfl ?_
    simp
  rw [toBall, hp, toEuclid_add_rf, ← axis_eq_toEuclid]

theorem measurePreserving_toBall (m : ℕ) : MeasurePreserving (toBall m) volume volume := by
  have h : MeasurePreserving
      ((fun x : EuclideanSpace ℝ (Fin (m + 1)) => x + axis m) ∘ toEuclid m) volume volume :=
    (measurePreserving_add_right volume (axis m)).comp (measurePreserving_toEuclid m)
  have hfun : toBall m = (fun x : EuclideanSpace ℝ (Fin (m + 1)) => x + axis m) ∘ toEuclid m :=
    funext toBall_eq_add
  rw [hfun]
  exact h

theorem measurePreserving_negShift_rf : MeasurePreserving (fun t : ℝ => -(t + 1)) volume volume := by
  have h : MeasurePreserving (Neg.neg ∘ fun t : ℝ => t + 1) volume volume :=
    (Measure.measurePreserving_neg volume).comp (measurePreserving_add_right volume 1)
  exact h

theorem measurePreserving_toBallNeg (m : ℕ) : MeasurePreserving (toBallNeg m) volume volume := by
  have hprod : MeasurePreserving
      (Prod.map (fun t : ℝ => -(t + 1)) (id : EuclideanSpace ℝ (Fin m) → _)) volume volume :=
    measurePreserving_negShift_rf.prod
      (MeasurePreserving.id (volume : Measure (EuclideanSpace ℝ (Fin m))))
  have h : MeasurePreserving
      (toEuclid m ∘ Prod.map (fun t : ℝ => -(t + 1)) (id : EuclideanSpace ℝ (Fin m) → _))
      volume volume := (measurePreserving_toEuclid m).comp hprod
  exact h

theorem measurable_toBall (m : ℕ) : Measurable (toBall m) :=
  (measurable_toEuclid m).comp ((measurable_fst.add_const 1).prodMk measurable_snd)

theorem measurable_toBallNeg (m : ℕ) : Measurable (toBallNeg m) :=
  (measurable_toEuclid m).comp ((measurable_fst.add_const 1).neg.prodMk measurable_snd)

theorem measurable_ofBall (m : ℕ) : Measurable (ofBall m) :=
  ((measurable_ofEuclid m).fst.sub_const 1).prodMk (measurable_ofEuclid m).snd

/-- The inverse of `toBallNeg`. -/
def ofBallNeg (m : ℕ) (x : EuclideanSpace ℝ (Fin (m + 1))) : CapSpace m :=
  (-x 0 - 1, (ofEuclid m x).2)

theorem measurable_ofBallNeg (m : ℕ) : Measurable (ofBallNeg m) :=
  ((measurable_ofEuclid m).fst.neg.sub_const 1).prodMk (measurable_ofEuclid m).snd

@[simp] theorem ofBallNeg_toBallNeg (p : CapSpace m) : ofBallNeg m (toBallNeg m p) = p := by
  refine Prod.ext ?_ ?_
  · show -(toBallNeg m p 0) - 1 = p.1
    rw [toBallNeg_apply_zero]; ring
  · exact PiLp.ext fun i => rfl

@[simp] theorem toBallNeg_ofBallNeg (x : EuclideanSpace ℝ (Fin (m + 1))) :
    toBallNeg m (ofBallNeg m x) = x := by
  have h : (-((ofBallNeg m x).1 + 1), (ofBallNeg m x).2) = ofEuclid m x := by
    refine Prod.ext ?_ rfl
    show -(-x 0 - 1 + 1) = x 0
    ring
  rw [toBallNeg, h, toEuclid_ofEuclid]

/-- `toBall` as a measurable equivalence. -/
def ballEquiv (m : ℕ) : CapSpace m ≃ᵐ EuclideanSpace ℝ (Fin (m + 1)) where
  toEquiv :=
    { toFun := toBall m, invFun := ofBall m, left_inv := ofBall_toBall, right_inv := toBall_ofBall }
  measurable_toFun := measurable_toBall m
  measurable_invFun := measurable_ofBall m

/-- `toBallNeg` as a measurable equivalence. -/
def ballEquivNeg (m : ℕ) : CapSpace m ≃ᵐ EuclideanSpace ℝ (Fin (m + 1)) where
  toEquiv :=
    { toFun := toBallNeg m, invFun := ofBallNeg m, left_inv := ofBallNeg_toBallNeg,
      right_inv := toBallNeg_ofBallNeg }
  measurable_toFun := measurable_toBallNeg m
  measurable_invFun := measurable_ofBallNeg m

theorem measurableEmbedding_toBall (m : ℕ) : MeasurableEmbedding (toBall m) :=
  (ballEquiv m).measurableEmbedding

theorem measurableEmbedding_toBallNeg (m : ℕ) : MeasurableEmbedding (toBallNeg m) :=
  (ballEquivNeg m).measurableEmbedding

theorem measurePreserving_ofBall (m : ℕ) : MeasurePreserving (ofBall m) volume volume :=
  (measurePreserving_toBall m).symm (ballEquiv m)

theorem measurePreserving_ofBallNeg (m : ℕ) : MeasurePreserving (ofBallNeg m) volume volume :=
  (measurePreserving_toBallNeg m).symm (ballEquivNeg m)

/-- Change of variables along `toBall` for set integrals. -/
theorem setIntegral_toBall (f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (s : Set (EuclideanSpace ℝ (Fin (m + 1)))) :
    ∫ p in toBall m ⁻¹' s, f (toBall m p) = ∫ x in s, f x :=
  (measurePreserving_toBall m).setIntegral_preimage_emb (measurableEmbedding_toBall m) f s

/-- Change of variables along `toBallNeg` for set integrals. -/
theorem setIntegral_toBallNeg (f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (s : Set (EuclideanSpace ℝ (Fin (m + 1)))) :
    ∫ p in toBallNeg m ⁻¹' s, f (toBallNeg m p) = ∫ x in s, f x :=
  (measurePreserving_toBallNeg m).setIntegral_preimage_emb (measurableEmbedding_toBallNeg m) f s

theorem integrableOn_toBall_iff {f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ}
    {s : Set (EuclideanSpace ℝ (Fin (m + 1)))} :
    IntegrableOn (fun p => f (toBall m p)) (toBall m ⁻¹' s) ↔ IntegrableOn f s :=
  (measurePreserving_toBall m).integrableOn_comp_preimage (measurableEmbedding_toBall m)

theorem integrableOn_toBallNeg_iff {f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ}
    {s : Set (EuclideanSpace ℝ (Fin (m + 1)))} :
    IntegrableOn (fun p => f (toBallNeg m p)) (toBallNeg m ⁻¹' s) ↔ IntegrableOn f s :=
  (measurePreserving_toBallNeg m).integrableOn_comp_preimage (measurableEmbedding_toBallNeg m)

/-! ## The equator is null and the ball splits -/

theorem volume_equator_rf :
    volume {x : EuclideanSpace ℝ (Fin (m + 1)) | x 0 = 0} = 0 := by
  have hms : MeasurableSet {p : CapSpace m | p.1 = 0} :=
    measurable_fst (measurableSet_singleton (0 : ℝ))
  have hset : {x : EuclideanSpace ℝ (Fin (m + 1)) | x 0 = 0}
      = ofEuclid m ⁻¹' {p : CapSpace m | p.1 = 0} := rfl
  rw [hset, (measurePreserving_ofEuclid m).measure_preimage hms.nullMeasurableSet]
  have hprod : {p : CapSpace m | p.1 = 0}
      = ({0} : Set ℝ) ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin m))) := by
    ext p; simp
  rw [hprod, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]

theorem ae_coord_ne_zero_rf :
    ∀ᵐ x : EuclideanSpace ℝ (Fin (m + 1)) ∂volume, x 0 ≠ 0 := by
  rw [ae_iff]
  simpa using volume_equator_rf (m := m)

theorem ball_ae_eq_union_rf :
    (ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
      =ᵐ[volume] (upperHalfBall m ∪ lowerHalfBall m :
        Set (EuclideanSpace ℝ (Fin (m + 1)))) := by
  rw [Filter.eventuallyEq_set]
  filter_upwards [ae_coord_ne_zero_rf (m := m)] with x hx
  simp only [mem_ball_zero_iff, Set.mem_union, upperHalfBall, lowerHalfBall, Set.mem_setOf_eq]
  constructor
  · intro h
    rcases lt_or_gt_of_ne hx with h0 | h0
    · exact Or.inr ⟨h, h0⟩
    · exact Or.inl ⟨h, h0⟩
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h

theorem restrict_ball_eq_rf :
    (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1))
      = volume.restrict (upperHalfBall m ∪ lowerHalfBall m) :=
  Measure.restrict_congr_set ball_ae_eq_union_rf

theorem disjoint_halfBalls_rf : Disjoint (upperHalfBall m) (lowerHalfBall m) := by
  rw [Set.disjoint_left]
  rintro x ⟨-, hx⟩ ⟨-, hx'⟩
  linarith

/-! ## Gluing the two halves -/

theorem measurableEmbedding_ofBall (m : ℕ) : MeasurableEmbedding (ofBall m) :=
  (ballEquiv m).symm.measurableEmbedding

theorem measurableEmbedding_ofBallNeg (m : ℕ) : MeasurableEmbedding (ofBallNeg m) :=
  (ballEquivNeg m).symm.measurableEmbedding

theorem ofBall_preimage_body :
    ofBall m ⁻¹' ((Cap.hemisphere m).body) = upperHalfBall m := by
  rw [← toBall_preimage_upper]
  ext x
  simp only [Set.mem_preimage, toBall_ofBall]

theorem ofBallNeg_preimage_body :
    ofBallNeg m ⁻¹' ((Cap.hemisphere m).body) = lowerHalfBall m := by
  rw [← toBallNeg_preimage_lower]
  ext x
  simp only [Set.mem_preimage, toBallNeg_ofBallNeg]

theorem measurePreserving_ofBall_upper (m : ℕ) :
    MeasurePreserving (ofBall m) (volume.restrict (upperHalfBall m))
      (volume.restrict ((Cap.hemisphere m).body)) := by
  have h := (measurePreserving_ofBall m).restrict_preimage_emb
    (measurableEmbedding_ofBall m) ((Cap.hemisphere m).body)
  rwa [ofBall_preimage_body] at h

theorem measurePreserving_ofBallNeg_lower (m : ℕ) :
    MeasurePreserving (ofBallNeg m) (volume.restrict (lowerHalfBall m))
      (volume.restrict ((Cap.hemisphere m).body)) := by
  have h := (measurePreserving_ofBallNeg m).restrict_preimage_emb
    (measurableEmbedding_ofBallNeg m) ((Cap.hemisphere m).body)
  rwa [ofBallNeg_preimage_body] at h

section Glue

variable {β : Type*} [NormedAddCommGroup β]

theorem memLp_upper_rf {F : EuclideanSpace ℝ (Fin (m + 1)) → β} {f : CapSpace m → β}
    (hf : MemLp f 2 (volume.restrict ((Cap.hemisphere m).body)))
    (hF : EqOn F (fun x => f (ofBall m x)) (upperHalfBall m)) :
    MemLp F 2 (volume.restrict (upperHalfBall m)) := by
  have h := hf.comp_measurePreserving (measurePreserving_ofBall_upper m)
  refine (memLp_congr_ae ?_).1 h
  exact (ae_restrict_iff' measurableSet_upperHalfBall).2
    (Filter.Eventually.of_forall fun x hx => (hF hx).symm)

theorem memLp_lower_rf {F : EuclideanSpace ℝ (Fin (m + 1)) → β} {g : CapSpace m → β}
    (hg : MemLp g 2 (volume.restrict ((Cap.hemisphere m).body)))
    (hF : EqOn F (fun x => g (ofBallNeg m x)) (lowerHalfBall m)) :
    MemLp F 2 (volume.restrict (lowerHalfBall m)) := by
  have h := hg.comp_measurePreserving (measurePreserving_ofBallNeg_lower m)
  refine (memLp_congr_ae ?_).1 h
  exact (ae_restrict_iff' measurableSet_lowerHalfBall).2
    (Filter.Eventually.of_forall fun x hx => (hF hx).symm)

/-- **Gluing lemma for `L²`**: a function of the unit ball which is the pull-back of an
`L²` function of the cap body on the upper half and (possibly another one) on the lower half is
in `L²` of the ball. -/
theorem memLp_ball_of_halves_rf {F : EuclideanSpace ℝ (Fin (m + 1)) → β} {f g : CapSpace m → β}
    (hf : MemLp f 2 (volume.restrict ((Cap.hemisphere m).body)))
    (hg : MemLp g 2 (volume.restrict ((Cap.hemisphere m).body)))
    (hF1 : EqOn F (fun x => f (ofBall m x)) (upperHalfBall m))
    (hF2 : EqOn F (fun x => g (ofBallNeg m x)) (lowerHalfBall m)) :
    MemLp F 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)) := by
  have h1 := memLp_upper_rf hf hF1
  have h2 := memLp_lower_rf hg hF2
  have haesm : AEStronglyMeasurable F
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)) := by
    rw [restrict_ball_eq_rf]
    exact aestronglyMeasurable_union_iff.2 ⟨h1.1, h2.1⟩
  refine (memLp_two_iff_integrable_sq_norm haesm).2 ?_
  have hi1 : IntegrableOn (fun x => ‖F x‖ ^ 2) (upperHalfBall m) :=
    (memLp_two_iff_integrable_sq_norm h1.1).1 h1
  have hi2 : IntegrableOn (fun x => ‖F x‖ ^ 2) (lowerHalfBall m) :=
    (memLp_two_iff_integrable_sq_norm h2.1).1 h2
  have hu := hi1.union hi2
  rw [show (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1))
    = volume.restrict (upperHalfBall m ∪ lowerHalfBall m) from restrict_ball_eq_rf]
  exact hu

end Glue

theorem integrableOn_upper_rf {F : EuclideanSpace ℝ (Fin (m + 1)) → ℝ} {f : CapSpace m → ℝ}
    (hf : IntegrableOn f ((Cap.hemisphere m).body))
    (hF : EqOn F (fun x => f (ofBall m x)) (upperHalfBall m)) :
    IntegrableOn F (upperHalfBall m) := by
  have hb : IntegrableOn (fun p => F (toBall m p)) ((Cap.hemisphere m).body) := by
    refine hf.congr_fun (fun p hp => ?_) measurableSet_body_rf
    have hmem : toBall m p ∈ upperHalfBall m := by
      rw [← toBall_preimage_upper] at hp; exact hp
    show f p = F (toBall m p)
    rw [hF hmem]
    show f p = f (ofBall m (toBall m p))
    rw [ofBall_toBall]
  rw [← toBall_preimage_upper] at hb
  exact integrableOn_toBall_iff.1 hb

theorem integrableOn_lower_rf {F : EuclideanSpace ℝ (Fin (m + 1)) → ℝ} {g : CapSpace m → ℝ}
    (hg : IntegrableOn g ((Cap.hemisphere m).body))
    (hF : EqOn F (fun x => g (ofBallNeg m x)) (lowerHalfBall m)) :
    IntegrableOn F (lowerHalfBall m) := by
  have hb : IntegrableOn (fun p => F (toBallNeg m p)) ((Cap.hemisphere m).body) := by
    refine hg.congr_fun (fun p hp => ?_) measurableSet_body_rf
    have hmem : toBallNeg m p ∈ lowerHalfBall m := by
      rw [← toBallNeg_preimage_lower] at hp; exact hp
    show g p = F (toBallNeg m p)
    rw [hF hmem]
    show g p = g (ofBallNeg m (toBallNeg m p))
    rw [ofBallNeg_toBallNeg]
  rw [← toBallNeg_preimage_lower] at hb
  exact integrableOn_toBallNeg_iff.1 hb

theorem setIntegral_upper_rf {F : EuclideanSpace ℝ (Fin (m + 1)) → ℝ} {f : CapSpace m → ℝ}
    (hF : EqOn F (fun x => f (ofBall m x)) (upperHalfBall m)) :
    ∫ x in upperHalfBall m, F x = ∫ p in (Cap.hemisphere m).body, f p := by
  rw [setIntegral_congr_fun measurableSet_upperHalfBall hF,
    ← setIntegral_toBall (fun x => f (ofBall m x)) (upperHalfBall m), toBall_preimage_upper]
  exact setIntegral_congr_fun measurableSet_body_rf fun p _ => by rw [ofBall_toBall]

theorem setIntegral_lower_rf {F : EuclideanSpace ℝ (Fin (m + 1)) → ℝ} {g : CapSpace m → ℝ}
    (hF : EqOn F (fun x => g (ofBallNeg m x)) (lowerHalfBall m)) :
    ∫ x in lowerHalfBall m, F x = ∫ p in (Cap.hemisphere m).body, g p := by
  rw [setIntegral_congr_fun measurableSet_lowerHalfBall hF,
    ← setIntegral_toBallNeg (fun x => g (ofBallNeg m x)) (lowerHalfBall m),
    toBallNeg_preimage_lower]
  exact setIntegral_congr_fun measurableSet_body_rf fun p _ => by rw [ofBallNeg_toBallNeg]

/-- **Gluing lemma for integrals.** -/
theorem setIntegral_ball_of_halves_rf {F : EuclideanSpace ℝ (Fin (m + 1)) → ℝ}
    {f g : CapSpace m → ℝ}
    (hf : IntegrableOn f ((Cap.hemisphere m).body))
    (hg : IntegrableOn g ((Cap.hemisphere m).body))
    (hF1 : EqOn F (fun x => f (ofBall m x)) (upperHalfBall m))
    (hF2 : EqOn F (fun x => g (ofBallNeg m x)) (lowerHalfBall m)) :
    ∫ x in ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1, F x
      = (∫ p in (Cap.hemisphere m).body, f p) + ∫ p in (Cap.hemisphere m).body, g p := by
  rw [show (∫ x in ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1, F x)
      = ∫ x in upperHalfBall m ∪ lowerHalfBall m, F x by rw [restrict_ball_eq_rf],
    setIntegral_union disjoint_halfBalls_rf measurableSet_lowerHalfBall
      (integrableOn_upper_rf hf hF1) (integrableOn_lower_rf hg hF2),
    setIntegral_upper_rf hF1, setIntegral_lower_rf hF2]

/-! ## The even reflection -/

/-- The sign of the axial coordinate (the value at `0` is irrelevant: the equator is null). -/
def sgn0 (x : EuclideanSpace ℝ (Fin (m + 1))) : ℝ := if x 0 < 0 then -1 else 1

theorem sgn0_of_nonneg {x : EuclideanSpace ℝ (Fin (m + 1))} (hx : 0 ≤ x 0) : sgn0 x = 1 :=
  if_neg (not_lt.2 hx)

theorem sgn0_of_neg {x : EuclideanSpace ℝ (Fin (m + 1))} (hx : x 0 < 0) : sgn0 x = -1 := if_pos hx

theorem capPt_eq_ofBallNeg {x : EuclideanSpace ℝ (Fin (m + 1))} (hx : x 0 ≤ 0) :
    capPt m x = ofBallNeg m x := by
  rw [capPt, ofBallNeg, abs_of_nonpos hx]

/-- The **even reflection** of a function of the cap body: `u(|t|-1, z)` in recentred
coordinates. -/
def reflectEvenFun (u : CapSpace m → ℝ) (x : EuclideanSpace ℝ (Fin (m + 1))) : ℝ := u (capPt m x)

/-- The gradient vector of the product model, read in `ℝ^{m+1}`. -/
def gradPair (gx : CapSpace m → ℝ) (gz : CapSpace m → EuclideanSpace ℝ (Fin m))
    (p : CapSpace m) : EuclideanSpace ℝ (Fin (m + 1)) := toEuclid m (gx p, gz p)

/-- The **reflected gradient**: the axial component is odd, the transverse one is even. -/
def reflectEvenGrad (gx : CapSpace m → ℝ) (gz : CapSpace m → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin (m + 1))) : EuclideanSpace ℝ (Fin (m + 1)) :=
  toEuclid m (sgn0 x * gx (capPt m x), gz (capPt m x))

theorem norm_gradPair_sq (gx : CapSpace m → ℝ) (gz : CapSpace m → EuclideanSpace ℝ (Fin m))
    (p : CapSpace m) : ‖gradPair gx gz p‖ ^ 2 = gx p ^ 2 + ‖gz p‖ ^ 2 :=
  norm_toEuclid_sq _

theorem norm_reflectEvenGrad_sq (gx : CapSpace m → ℝ)
    (gz : CapSpace m → EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin (m + 1))) :
    ‖reflectEvenGrad gx gz x‖ ^ 2 = gx (capPt m x) ^ 2 + ‖gz (capPt m x)‖ ^ 2 := by
  rw [reflectEvenGrad, norm_toEuclid_sq]
  have h : sgn0 x ^ 2 = 1 := by
    rcases lt_or_ge (x 0) 0 with h | h
    · rw [sgn0_of_neg h]; norm_num
    · rw [sgn0_of_nonneg h]; norm_num
  have : (sgn0 x * gx (capPt m x)) ^ 2 = sgn0 x ^ 2 * gx (capPt m x) ^ 2 := by ring
  rw [this, h, one_mul]

theorem reflectEvenFun_eqOn_upper (u : CapSpace m → ℝ) :
    EqOn (reflectEvenFun u) (fun x => u (ofBall m x)) (upperHalfBall m) := fun _ hx => by
  rw [reflectEvenFun, capPt_eq_ofBall hx.2.le]

theorem reflectEvenFun_eqOn_lower (u : CapSpace m → ℝ) :
    EqOn (reflectEvenFun u) (fun x => u (ofBallNeg m x)) (lowerHalfBall m) := fun _ hx => by
  rw [reflectEvenFun, capPt_eq_ofBallNeg hx.2.le]

theorem reflectEvenGrad_eqOn_upper (gx : CapSpace m → ℝ)
    (gz : CapSpace m → EuclideanSpace ℝ (Fin m)) :
    EqOn (reflectEvenGrad gx gz) (fun x => gradPair gx gz (ofBall m x)) (upperHalfBall m) :=
  fun x hx => by
  show toEuclid m (sgn0 x * gx (capPt m x), gz (capPt m x))
      = toEuclid m (gx (ofBall m x), gz (ofBall m x))
  rw [capPt_eq_ofBall hx.2.le, sgn0_of_nonneg hx.2.le, one_mul]

theorem reflectEvenGrad_eqOn_lower (gx : CapSpace m → ℝ)
    (gz : CapSpace m → EuclideanSpace ℝ (Fin m)) :
    EqOn (reflectEvenGrad gx gz) (fun x => gradPair (fun p => -gx p) gz (ofBallNeg m x))
      (lowerHalfBall m) := fun x hx => by
  show toEuclid m (sgn0 x * gx (capPt m x), gz (capPt m x))
      = toEuclid m (-gx (ofBallNeg m x), gz (ofBallNeg m x))
  rw [capPt_eq_ofBallNeg hx.2.le, sgn0_of_neg hx.2, neg_one_mul]

theorem aestronglyMeasurable_gradPair {μ : Measure (CapSpace m)} {gx : CapSpace m → ℝ}
    {gz : CapSpace m → EuclideanSpace ℝ (Fin m)} (hgx : AEStronglyMeasurable gx μ)
    (hgz : AEStronglyMeasurable gz μ) : AEStronglyMeasurable (gradPair gx gz) μ :=
  ((measurable_toEuclid m).comp_aemeasurable
    (hgx.aemeasurable.prodMk hgz.aemeasurable)).aestronglyMeasurable

theorem memLp_gradPair {μ : Measure (CapSpace m)} {gx : CapSpace m → ℝ}
    {gz : CapSpace m → EuclideanSpace ℝ (Fin m)} (hgx : MemLp gx 2 μ) (hgz : MemLp gz 2 μ) :
    MemLp (gradPair gx gz) 2 μ := by
  refine (memLp_two_iff_integrable_sq_norm
    (aestronglyMeasurable_gradPair hgx.1 hgz.1)).2 ?_
  have h := hgx.integrable_sq.add ((memLp_two_iff_integrable_sq_norm hgz.1).1 hgz)
  refine h.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [Pi.add_apply]
  rw [norm_gradPair_sq]

/-! ## The axial cut-off near the entrance face -/

/-- The smooth axial cut-off: `0` for `s + 1 ≤ ε`, `1` for `s + 1 ≥ 2ε`. -/
def faceCut (ε : ℝ) (p : CapSpace m) : ℝ := Real.smoothTransition ((p.1 + 1) / ε - 1)

theorem faceCut_contDiff (ε : ℝ) : ContDiff ℝ ∞ (faceCut ε : CapSpace m → ℝ) := by
  have h : ContDiff ℝ ∞ fun p : CapSpace m => (p.1 + 1) / ε - 1 :=
    ((contDiff_fst.add contDiff_const).div_const ε).sub contDiff_const
  exact Real.smoothTransition.contDiff.comp h

theorem faceCut_nonneg (ε : ℝ) (p : CapSpace m) : 0 ≤ faceCut ε p :=
  Real.smoothTransition.nonneg _

theorem faceCut_le_one (ε : ℝ) (p : CapSpace m) : faceCut ε p ≤ 1 :=
  Real.smoothTransition.le_one _

theorem faceCut_eq_zero {ε : ℝ} (hε : 0 < ε) {p : CapSpace m} (h : p.1 + 1 ≤ ε) :
    faceCut ε p = 0 :=
  Real.smoothTransition.zero_of_nonpos (by rw [sub_nonpos, div_le_one hε]; exact h)

theorem faceCut_eq_one {ε : ℝ} (hε : 0 < ε) {p : CapSpace m} (h : 2 * ε ≤ p.1 + 1) :
    faceCut ε p = 1 :=
  Real.smoothTransition.one_of_one_le (by rw [le_sub_iff_add_le, le_div_iff₀ hε]; linarith)

theorem faceCut_support {ε : ℝ} (hε : 0 < ε) :
    tsupport (faceCut ε : CapSpace m → ℝ) ⊆ {p : CapSpace m | ε ≤ p.1 + 1} := by
  refine closure_minimal (fun p hp => ?_) ?_
  · by_contra hcon
    exact hp (faceCut_eq_zero hε (le_of_lt (by simpa using not_le.1 hcon)))
  · exact isClosed_le continuous_const (continuous_fst.add continuous_const)

theorem hasDerivAt_faceCut1 (ε : ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.smoothTransition ((s + 1) / ε - 1))
      (deriv Real.smoothTransition ((t + 1) / ε - 1) * (1 / ε)) t := by
  have hg : HasDerivAt (fun s : ℝ => (s + 1) / ε - 1) (1 / ε) t := by
    have h1 : HasDerivAt (fun s : ℝ => (s + 1) / ε) (1 / ε) t := by
      simpa using ((hasDerivAt_id t).add_const (1 : ℝ)).div_const ε
    simpa using h1.sub_const 1
  have hs : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition ((t + 1) / ε - 1)) ((t + 1) / ε - 1) :=
    ((Real.smoothTransition.contDiff (n := (1 : ℕ∞))).differentiable (by simp)
      ((t + 1) / ε - 1)).hasDerivAt
  exact hs.comp t hg

theorem fderiv_faceCut_apply (ε : ℝ) (p v : CapSpace m) :
    fderiv ℝ (faceCut ε) p v
      = deriv Real.smoothTransition ((p.1 + 1) / ε - 1) * (1 / ε) * v.1 := by
  have hcomp : HasFDerivAt (faceCut ε)
      ((deriv Real.smoothTransition ((p.1 + 1) / ε - 1) * (1 / ε)) •
        (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin m)))) p :=
    (hasDerivAt_faceCut1 ε p.1).comp_hasFDerivAt p (hasFDerivAt_fst)
  rw [hcomp.fderiv]
  simp

theorem fderiv_mul_faceCut (ε : ℝ) {Ψ : CapSpace m → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (p v : CapSpace m) :
    fderiv ℝ (fun q => Ψ q * faceCut ε q) p v
      = faceCut ε p * fderiv ℝ Ψ p v
        + Ψ p * (deriv Real.smoothTransition ((p.1 + 1) / ε - 1) * (1 / ε) * v.1) := by
  have hd : HasFDerivAt (fun q : CapSpace m => Ψ q * faceCut ε q)
      (Ψ p • fderiv ℝ (faceCut ε) p + faceCut ε p • fderiv ℝ Ψ p) p :=
    ((hΨ.differentiable (by simp)) p).hasFDerivAt.mul
      (((faceCut_contDiff ε).differentiable (by simp)) p).hasFDerivAt
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    fderiv_faceCut_apply]
  ring

/-! ### The derivative of the smooth transition is bounded and vanishes outside `[0,1]` -/

theorem deriv_smoothTransition_eq_zero_of_one_lt {y : ℝ} (hy : 1 < y) :
    deriv Real.smoothTransition y = 0 := by
  have hev : Real.smoothTransition =ᶠ[nhds y] fun _ => (1 : ℝ) := by
    filter_upwards [isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hy)] with z hz
    exact Real.smoothTransition.one_of_one_le (le_of_lt hz)
  rw [hev.deriv_eq, deriv_const]

theorem deriv_smoothTransition_eq_zero_of_lt_zero {y : ℝ} (hy : y < 0) :
    deriv Real.smoothTransition y = 0 := by
  have hev : Real.smoothTransition =ᶠ[nhds y] fun _ => (0 : ℝ) := by
    filter_upwards [isOpen_Iio.mem_nhds (Set.mem_Iio.mpr hy)] with z hz
    exact Real.smoothTransition.zero_of_nonpos (le_of_lt hz)
  rw [hev.deriv_eq, deriv_const]

theorem hasCompactSupport_deriv_smoothTransition :
    HasCompactSupport (deriv Real.smoothTransition) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 1)) fun y hy => ?_
  rcases not_and_or.1 (fun h => hy (Set.mem_Icc.2 h)) with h | h
  · exact deriv_smoothTransition_eq_zero_of_lt_zero (not_le.1 h)
  · exact deriv_smoothTransition_eq_zero_of_one_lt (not_le.1 h)

theorem exists_bound_deriv_smoothTransition :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : ℝ, |deriv Real.smoothTransition y| ≤ M := by
  obtain ⟨M, hM⟩ := hasCompactSupport_deriv_smoothTransition.exists_bound_of_continuous
    ((Real.smoothTransition.contDiff (n := (1 : ℕ∞))).continuous_deriv (by simp))
  refine ⟨M, le_trans (abs_nonneg _) (hM 0), fun y => ?_⟩
  simpa [Real.norm_eq_abs] using hM y

/-! ## Test functions reaching the entrance face -/

theorem volume_capQ_rf :
    volume (capQ m) = volume (ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) := by
  rw [← toBall_preimage_ball]
  exact (measurePreserving_toBall m).measure_preimage measurableSet_ball.nullMeasurableSet

theorem volume_body_lt_top : volume ((Cap.hemisphere m).body) < ⊤ := by
  have h1 : volume ((Cap.hemisphere m).body) ≤ volume (capQ m) := by
    refine measure_mono ?_
    rw [body_eq_capQ_inter]
    exact Set.inter_subset_left
  refine lt_of_le_of_lt h1 ?_
  rw [volume_capQ_rf]
  exact measure_ball_lt_top

instance isFiniteMeasure_body_rf :
    IsFiniteMeasure (volume.restrict ((Cap.hemisphere m).body)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact volume_body_lt_top⟩

theorem tsupport_mul_faceCut {ε : ℝ} (hε : 0 < ε) {Ψ : CapSpace m → ℝ}
    (hΨs : tsupport Ψ ⊆ capQ m) :
    tsupport (fun q => Ψ q * faceCut ε q) ⊆ (Cap.hemisphere m).body := by
  have h1 : tsupport (fun q : CapSpace m => Ψ q * faceCut ε q) ⊆ tsupport Ψ :=
    closure_mono (Function.support_mul_subset_left _ _)
  have h2 : tsupport (fun q : CapSpace m => Ψ q * faceCut ε q) ⊆ tsupport (faceCut ε) :=
    closure_mono (Function.support_mul_subset_right _ _)
  intro p hp
  have hq : p ∈ capQ m := hΨs (h1 hp)
  have hs : ε ≤ p.1 + 1 := faceCut_support hε (h2 hp)
  rw [body_eq_capQ_inter]
  exact ⟨hq, by simp only [Set.mem_setOf_eq]; linarith⟩

/-- The cut-off integrals converge to the full integral. -/
theorem tendsto_mul_faceCut {F : CapSpace m → ℝ}
    (hF : IntegrableOn F ((Cap.hemisphere m).body)) :
    Filter.Tendsto (fun ε : ℝ => ∫ p in (Cap.hemisphere m).body, F p * faceCut ε p)
      (nhdsWithin 0 (Set.Ioi (0:ℝ))) (nhds (∫ p in (Cap.hemisphere m).body, F p)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun p => |F p|) ?_ ?_ hF.abs ?_
  · filter_upwards [self_mem_nhdsWithin] with ε _
    exact hF.1.mul ((faceCut_contDiff ε).continuous.aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin] with ε _
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (faceCut_nonneg ε p)]
    exact mul_le_of_le_one_right (abs_nonneg _) (faceCut_le_one ε p)
  · filter_upwards [ae_restrict_mem measurableSet_body_rf] with p hp
    have hp1 : -1 < p.1 := (mem_hemisphere_body_iff.1 hp).1
    have hmem : Set.Ioo (0:ℝ) ((p.1 + 1)/2) ∈ nhdsWithin 0 (Set.Ioi (0:ℝ)) :=
      Ioo_mem_nhdsGT (by linarith)
    refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := F p))
    filter_upwards [hmem] with ε hε
    rw [faceCut_eq_one hε.1 (by linarith [hε.2]), mul_one]

/-- The error term produced by differentiating the cut-off tends to zero, provided the test
function vanishes on the entrance face (so that it is `O(s+1)` there). -/
theorem tendsto_faceCut_error {v Ψ : CapSpace m → ℝ}
    (hv : IntegrableOn v ((Cap.hemisphere m).body))
    (hΨcont : Continuous Ψ) {L : ℝ} (hL0 : 0 ≤ L)
    (hLb : ∀ p : CapSpace m, -1 ≤ p.1 → |Ψ p| ≤ L * (p.1 + 1)) :
    Filter.Tendsto (fun ε : ℝ => ∫ p in (Cap.hemisphere m).body,
        v p * (Ψ p * (deriv Real.smoothTransition ((p.1 + 1) / ε - 1) * (1 / ε))))
      (nhdsWithin 0 (Set.Ioi (0:ℝ))) (nhds 0) := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_deriv_smoothTransition
  suffices hmain : Filter.Tendsto (fun ε : ℝ => ∫ p in (Cap.hemisphere m).body,
      v p * (Ψ p * (deriv Real.smoothTransition ((p.1 + 1) / ε - 1) * (1 / ε))))
      (nhdsWithin 0 (Set.Ioi (0:ℝ)))
      (nhds (∫ _p in (Cap.hemisphere m).body, (0:ℝ))) by simpa using hmain
  refine tendsto_integral_filter_of_dominated_convergence
    (fun p => 2 * L * M * |v p|) ?_ ?_ (hv.abs.const_mul _) ?_
  · filter_upwards [self_mem_nhdsWithin] with ε _
    have hc : Continuous fun p : CapSpace m =>
        Ψ p * (deriv Real.smoothTransition ((p.1 + 1) / ε - 1) * (1 / ε)) := by
      refine hΨcont.mul (Continuous.mul ?_ continuous_const)
      exact ((Real.smoothTransition.contDiff (n := (1 : ℕ∞))).continuous_deriv (by simp)).comp
        (((continuous_fst.add continuous_const).div_const ε).sub continuous_const)
    exact hv.1.mul hc.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards [ae_restrict_mem measurableSet_body_rf] with p hp
    have hε0 : (0:ℝ) < ε := hε
    have hp1 : -1 < p.1 := (mem_hemisphere_body_iff.1 hp).1
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
    have habs : |Ψ p| * (|deriv Real.smoothTransition ((p.1 + 1) / ε - 1)| * |1/ε|)
        ≤ 2 * L * M := by
      rcases lt_or_ge (1 : ℝ) ((p.1 + 1) / ε - 1) with hcase | hcase
      · rw [deriv_smoothTransition_eq_zero_of_one_lt hcase]
        simp only [abs_zero, zero_mul, mul_zero]
        positivity
      · have h2 : p.1 + 1 ≤ 2 * ε := by
          have := (div_le_iff₀ hε0).1 (by linarith : (p.1 + 1)/ε ≤ 2)
          linarith
        have hΨ1 : |Ψ p| ≤ L * (p.1 + 1) := hLb p hp1.le
        have hinv : |1/ε| = 1/ε := abs_of_pos (by positivity)
        have hd : |deriv Real.smoothTransition ((p.1 + 1) / ε - 1)| ≤ M := hM _
        have hstep : |Ψ p| * (1/ε) ≤ 2 * L := by
          rw [mul_one_div, div_le_iff₀ hε0]
          calc |Ψ p| ≤ L * (p.1 + 1) := hΨ1
            _ ≤ L * (2 * ε) := by nlinarith
            _ = 2 * L * ε := by ring
        calc |Ψ p| * (|deriv Real.smoothTransition ((p.1 + 1) / ε - 1)| * |1/ε|)
            = (|Ψ p| * (1/ε)) * |deriv Real.smoothTransition ((p.1 + 1) / ε - 1)| := by
              rw [hinv]; ring
          _ ≤ (2 * L) * M := by
              refine mul_le_mul hstep hd (abs_nonneg _) (by positivity)
          _ = 2 * L * M := by ring
    calc |v p| * (|Ψ p| * (|deriv Real.smoothTransition ((p.1 + 1) / ε - 1)| * |1/ε|))
        ≤ |v p| * (2 * L * M) := mul_le_mul_of_nonneg_left habs (abs_nonneg _)
      _ = 2 * L * M * |v p| := by ring
  · filter_upwards [ae_restrict_mem measurableSet_body_rf] with p hp
    have hp1 : -1 < p.1 := (mem_hemisphere_body_iff.1 hp).1
    have hmem : Set.Ioo (0:ℝ) ((p.1 + 1)/4) ∈ nhdsWithin 0 (Set.Ioi (0:ℝ)) :=
      Ioo_mem_nhdsGT (by linarith)
    refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := (0:ℝ)))
    filter_upwards [hmem] with ε hε
    have hgt : 1 < (p.1 + 1) / ε - 1 := by
      have h4 : 4 * ε < p.1 + 1 := by
        have := hε.2
        linarith
      have h2 : 2 < (p.1 + 1) / ε := by
        rw [lt_div_iff₀ hε.1]; linarith
      linarith
    rw [deriv_smoothTransition_eq_zero_of_one_lt hgt]
    ring

/-! ### The two weak-derivative identities up to the entrance face -/

/-- **Transverse direction.**  The weak-derivative identity of `u` holds for test functions whose
support reaches the entrance face `s = -1` (the face is not touched by the transverse
directions). -/
theorem weakGrad_transverse_face (u : H1P ((Cap.hemisphere m).body)) {Ψ : CapSpace m → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hΨc : HasCompactSupport Ψ) (hΨs : tsupport Ψ ⊆ capQ m) (i : Fin m) :
    ∫ p in (Cap.hemisphere m).body,
        u.toFun p * fderiv ℝ Ψ p ((0 : ℝ), EuclideanSpace.single i (1 : ℝ))
      = -∫ p in (Cap.hemisphere m).body, u.gz p i * Ψ p := by
  have hint1 : IntegrableOn (fun p => u.toFun p *
      fderiv ℝ Ψ p ((0 : ℝ), EuclideanSpace.single i (1 : ℝ))) ((Cap.hemisphere m).body) :=
    u.memL2.integrable_mul (memLp_two_dirDeriv hΨ hΨc _)
  have hint2 : IntegrableOn (fun p => u.gz p i * Ψ p) ((Cap.hemisphere m).body) :=
    integrable_compP_mul u.gz_memL2 hΨ hΨc i
  have key : ∀ ε : ℝ, ε ∈ Set.Ioi (0:ℝ) →
      -(∫ p in (Cap.hemisphere m).body, (u.gz p i * Ψ p) * faceCut ε p)
        = ∫ p in (Cap.hemisphere m).body,
            (u.toFun p * fderiv ℝ Ψ p ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)))
              * faceCut ε p := by
    intro ε hε
    have hw := (u.hasWeakGrad (fun q => Ψ q * faceCut ε q) (hΨ.mul (faceCut_contDiff ε))
      hΨc.mul_right (tsupport_mul_faceCut hε hΨs)).2 i
    have e1 : (∫ p in (Cap.hemisphere m).body,
          (u.toFun p * fderiv ℝ Ψ p ((0 : ℝ), EuclideanSpace.single i (1 : ℝ))) * faceCut ε p)
        = ∫ p in (Cap.hemisphere m).body, u.toFun p *
            fderiv ℝ (fun q => Ψ q * faceCut ε q) p
              ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)) := by
      refine setIntegral_congr_fun measurableSet_body_rf fun p _ => ?_
      have hz : ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)).1 = 0 := rfl
      rw [fderiv_mul_faceCut ε hΨ p ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)), hz, mul_zero,
        mul_zero, add_zero]
      ring
    have e2 : (∫ p in (Cap.hemisphere m).body, u.gz p i * (Ψ p * faceCut ε p))
        = ∫ p in (Cap.hemisphere m).body, (u.gz p i * Ψ p) * faceCut ε p :=
      setIntegral_congr_fun measurableSet_body_rf fun p _ => by ring
    rw [e1, hw, e2]
  have hL := tendsto_mul_faceCut hint1
  have hR := (tendsto_mul_faceCut hint2).neg
  refine tendsto_nhds_unique hL ?_
  refine Filter.Tendsto.congr' ?_ hR
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact key ε hε

/-- **Axial direction.**  The weak-derivative identity of `u` holds for test functions whose
support reaches the entrance face `s = -1`, *provided they vanish on that face*.  This is the
key step of the even reflection: the odd part of a test function of the ball vanishes there. -/
theorem weakGrad_axial_face (u : H1P ((Cap.hemisphere m).body)) {Ψ : CapSpace m → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hΨc : HasCompactSupport Ψ) (hΨs : tsupport Ψ ⊆ capQ m)
    (hface : ∀ z : EuclideanSpace ℝ (Fin m), Ψ ((-1 : ℝ), z) = 0) :
    ∫ p in (Cap.hemisphere m).body,
        u.toFun p * fderiv ℝ Ψ p ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m)))
      = -∫ p in (Cap.hemisphere m).body, u.gx p * Ψ p := by
  obtain ⟨L, hLip⟩ := hΨ.lipschitzWith_of_hasCompactSupport hΨc (by simp)
  have hLb : ∀ p : CapSpace m, -1 ≤ p.1 → |Ψ p| ≤ (L : ℝ) * (p.1 + 1) := by
    intro p hp
    have hd := hLip.dist_le_mul p ((-1 : ℝ), p.2)
    have hdist : dist p ((-1 : ℝ), p.2) = p.1 + 1 := by
      rw [Prod.dist_eq, dist_self, Real.dist_eq]
      rw [max_eq_left (abs_nonneg _), abs_of_nonneg (by linarith : (0:ℝ) ≤ p.1 - -1)]
      ring
    rw [Real.dist_eq, hface p.2, sub_zero, hdist] at hd
    exact hd
  have huint : IntegrableOn u.toFun ((Cap.hemisphere m).body) := u.memL2.integrable one_le_two
  have hint1 : IntegrableOn (fun p => u.toFun p *
      fderiv ℝ Ψ p ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m)))) ((Cap.hemisphere m).body) :=
    u.memL2.integrable_mul (memLp_two_dirDeriv hΨ hΨc _)
  have hint2 : IntegrableOn (fun p => u.gx p * Ψ p) ((Cap.hemisphere m).body) :=
    integrable_gx_mul u.gx_memL2 hΨ hΨc
  have hcontd : ∀ ε : ℝ, Continuous fun p : CapSpace m =>
      deriv Real.smoothTransition ((p.1 + 1) / ε - 1) * (1 / ε) := by
    intro ε
    refine Continuous.mul ?_ continuous_const
    exact ((Real.smoothTransition.contDiff (n := (1 : ℕ∞))).continuous_deriv (by simp)).comp
      (((continuous_fst.add continuous_const).div_const ε).sub continuous_const)
  have hintA : ∀ ε : ℝ, IntegrableOn (fun p => (u.toFun p *
      fderiv ℝ Ψ p ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m)))) * faceCut ε p)
      ((Cap.hemisphere m).body) := by
    intro ε
    have hc : Continuous fun p : CapSpace m =>
        fderiv ℝ Ψ p ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))) * faceCut ε p :=
      ((hΨ.continuous_fderiv (by simp)).clm_apply continuous_const).mul
        (faceCut_contDiff ε).continuous
    have hcc : HasCompactSupport fun p : CapSpace m =>
        fderiv ℝ Ψ p ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))) * faceCut ε p :=
      (hΨc.fderiv_apply ℝ _).mul_right
    refine (u.memL2.integrable_mul
      (Continuous.memLp_of_hasCompactSupport (p := 2) hc hcc)).congr ?_
    refine Filter.Eventually.of_forall fun p => ?_
    simp only [Pi.mul_apply]
    ring
  have hintE : ∀ ε : ℝ, IntegrableOn (fun p => u.toFun p *
      (Ψ p * (deriv Real.smoothTransition ((p.1 + 1) / ε - 1) * (1 / ε))))
      ((Cap.hemisphere m).body) := by
    intro ε
    exact u.memL2.integrable_mul (Continuous.memLp_of_hasCompactSupport (p := 2)
      (hΨ.continuous.mul (hcontd ε)) hΨc.mul_right)
  have key : ∀ ε : ℝ, ε ∈ Set.Ioi (0:ℝ) →
      -(∫ p in (Cap.hemisphere m).body, (u.gx p * Ψ p) * faceCut ε p)
        = (∫ p in (Cap.hemisphere m).body, (u.toFun p *
            fderiv ℝ Ψ p ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m)))) * faceCut ε p)
          + ∫ p in (Cap.hemisphere m).body, u.toFun p *
            (Ψ p * (deriv Real.smoothTransition ((p.1 + 1) / ε - 1) * (1 / ε))) := by
    intro ε hε
    have hw := (u.hasWeakGrad (fun q => Ψ q * faceCut ε q) (hΨ.mul (faceCut_contDiff ε))
      hΨc.mul_right (tsupport_mul_faceCut hε hΨs)).1
    have e1 : (∫ p in (Cap.hemisphere m).body, u.toFun p *
          fderiv ℝ (fun q => Ψ q * faceCut ε q) p ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))))
        = (∫ p in (Cap.hemisphere m).body, (u.toFun p *
            fderiv ℝ Ψ p ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m)))) * faceCut ε p)
          + ∫ p in (Cap.hemisphere m).body, u.toFun p *
            (Ψ p * (deriv Real.smoothTransition ((p.1 + 1) / ε - 1) * (1 / ε))) := by
      rw [← integral_add (hintA ε) (hintE ε)]
      refine setIntegral_congr_fun measurableSet_body_rf fun p _ => ?_
      have hz : ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))).1 = 1 := rfl
      rw [fderiv_mul_faceCut ε hΨ p ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))), hz, mul_one]
      ring
    have e2 : (∫ p in (Cap.hemisphere m).body, u.gx p * (Ψ p * faceCut ε p))
        = ∫ p in (Cap.hemisphere m).body, (u.gx p * Ψ p) * faceCut ε p :=
      setIntegral_congr_fun measurableSet_body_rf fun p _ => by ring
    rw [← e1, hw, e2]
  have hL := (tendsto_mul_faceCut hint1).add
    (tendsto_faceCut_error huint hΨ.continuous L.coe_nonneg hLb)
  have hR := (tendsto_mul_faceCut hint2).neg
  rw [show (∫ p in (Cap.hemisphere m).body, u.toFun p *
      fderiv ℝ Ψ p ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))))
      = (∫ p in (Cap.hemisphere m).body, u.toFun p *
        fderiv ℝ Ψ p ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m)))) + 0 by ring]
  refine tendsto_nhds_unique hL ?_
  refine Filter.Tendsto.congr' ?_ hR
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact key ε hε

/-! ## Pulling test functions of the ball back to the cap body -/

theorem toEuclid_smul_rf (c : ℝ) (p : CapSpace m) :
    toEuclid m (c • p) = c • toEuclid m p := by
  refine PiLp.ext fun j => ?_
  refine Fin.cases ?_ (fun i => ?_) j
  · simp
  · simp

/-- The identification `CapSpace m ≃ ℝ^{m+1}` as a continuous linear equivalence. -/
def capLinearEquiv (m : ℕ) : CapSpace m ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := toEuclid m, invFun := ofEuclid m, map_add' := toEuclid_add_rf,
      map_smul' := toEuclid_smul_rf, left_inv := ofEuclid_toEuclid,
      right_inv := toEuclid_ofEuclid }

@[simp] theorem capLinearEquiv_apply (p : CapSpace m) : capLinearEquiv m p = toEuclid m p := rfl

/-- The linear part of `toBall`, as a continuous linear map. -/
def toEuclidL (m : ℕ) : CapSpace m →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
  (capLinearEquiv m).toContinuousLinearMap

@[simp] theorem toEuclidL_apply (p : CapSpace m) : toEuclidL m p = toEuclid m p := rfl

/-- The reflection of the axial coordinate, as a continuous linear map. -/
def negFstL (m : ℕ) : CapSpace m →L[ℝ] CapSpace m :=
  ContinuousLinearMap.prod (-(ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin m))))
    (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin m)))

@[simp] theorem negFstL_apply (p : CapSpace m) : negFstL m p = (-p.1, p.2) := rfl

theorem toEuclid_single_succ (i : Fin m) :
    toEuclid m ((0 : ℝ), EuclideanSpace.single i (1 : ℝ))
      = EuclideanSpace.single i.succ (1 : ℝ) := by
  refine PiLp.ext fun j => ?_
  refine Fin.cases ?_ (fun k => ?_) j
  · have hne0 : ¬ ((0 : Fin (m + 1)) = i.succ) := fun h => Fin.succ_ne_zero i h.symm
    simp [EuclideanSpace.single_apply, hne0]
  · by_cases hk : k = i
    · subst hk; simp [EuclideanSpace.single_apply]
    · have hne : ¬ (k.succ = i.succ) := fun h => hk (Fin.succ_injective _ h)
      simp [EuclideanSpace.single_apply, hk, hne]

theorem toEuclid_one_zero :
    toEuclid m ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m)))
      = EuclideanSpace.single (0 : Fin (m + 1)) (1 : ℝ) := by
  rw [← axis_eq_toEuclid]
  rfl

theorem toEuclid_neg_one_zero :
    toEuclid m ((-1 : ℝ), (0 : EuclideanSpace ℝ (Fin m)))
      = -EuclideanSpace.single (0 : Fin (m + 1)) (1 : ℝ) := by
  have h : ((-1 : ℝ), (0 : EuclideanSpace ℝ (Fin m)))
      = (-1 : ℝ) • ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))) := by
    refine Prod.ext ?_ ?_ <;> simp
  rw [h, toEuclid_smul_rf, toEuclid_one_zero]
  simp

theorem toBallNeg_eq_sub (p : CapSpace m) :
    toBallNeg m p = toEuclid m (negFstL m p) - axis m := by
  refine PiLp.ext fun j => ?_
  refine Fin.cases ?_ (fun i => ?_) j
  · show -(p.1 + 1) = toEuclid m (-p.1, p.2) 0 - axis m 0
    simp [axis, EuclideanSpace.single_apply]
    ring
  · show p.2 i = toEuclid m (-p.1, p.2) i.succ - axis m i.succ
    simp [axis, EuclideanSpace.single_apply, Fin.succ_ne_zero]

theorem hasFDerivAt_toBall (p : CapSpace m) : HasFDerivAt (toBall m) (toEuclidL m) p := by
  have h : HasFDerivAt (fun q : CapSpace m => toEuclidL m q + axis m) (toEuclidL m) p :=
    (toEuclidL m).hasFDerivAt.add_const _
  have hfun : (fun q : CapSpace m => toEuclidL m q + axis m) = toBall m :=
    funext fun q => (toBall_eq_add q).symm
  rwa [hfun] at h

theorem hasFDerivAt_toBallNeg (p : CapSpace m) :
    HasFDerivAt (toBallNeg m) ((toEuclidL m).comp (negFstL m)) p := by
  have h : HasFDerivAt (fun q : CapSpace m => toEuclidL m (negFstL m q) - axis m)
      ((toEuclidL m).comp (negFstL m)) p :=
    ((toEuclidL m).comp (negFstL m)).hasFDerivAt.sub_const _
  have hfun : (fun q : CapSpace m => toEuclidL m (negFstL m q) - axis m) = toBallNeg m :=
    funext fun q => (toBallNeg_eq_sub q).symm
  rwa [hfun] at h

theorem contDiff_toBall : ContDiff ℝ ∞ (toBall m) := by
  have hfun : (fun q : CapSpace m => toEuclidL m q + axis m) = toBall m :=
    funext fun q => (toBall_eq_add q).symm
  rw [← hfun]
  exact (toEuclidL m).contDiff.add contDiff_const

theorem contDiff_toBallNeg : ContDiff ℝ ∞ (toBallNeg m) := by
  have hfun : (fun q : CapSpace m => toEuclidL m (negFstL m q) - axis m) = toBallNeg m :=
    funext fun q => (toBallNeg_eq_sub q).symm
  rw [← hfun]
  exact (((toEuclidL m).comp (negFstL m)).contDiff).sub contDiff_const

/-- `toBall` as a homeomorphism (used only for compactness of supports). -/
def toBallHomeo (m : ℕ) : CapSpace m ≃ₜ EuclideanSpace ℝ (Fin (m + 1)) :=
  (capLinearEquiv m).toHomeomorph.trans (Homeomorph.addRight (axis m))

@[simp] theorem toBallHomeo_apply (p : CapSpace m) : toBallHomeo m p = toBall m p :=
  (toBall_eq_add p).symm

/-- The axial reflection of the product model, as a homeomorphism. -/
def negFstHomeo (m : ℕ) : CapSpace m ≃ₜ CapSpace m where
  toFun := fun p => (-p.1, p.2)
  invFun := fun p => (-p.1, p.2)
  left_inv := fun p => by simp
  right_inv := fun p => by simp
  continuous_toFun := (negFstL m).continuous
  continuous_invFun := (negFstL m).continuous

/-- `toBallNeg` as a homeomorphism. -/
def toBallNegHomeo (m : ℕ) : CapSpace m ≃ₜ EuclideanSpace ℝ (Fin (m + 1)) :=
  (negFstHomeo m).trans ((capLinearEquiv m).toHomeomorph.trans (Homeomorph.subRight (axis m)))

@[simp] theorem toBallNegHomeo_apply (p : CapSpace m) : toBallNegHomeo m p = toBallNeg m p :=
  (toBallNeg_eq_sub p).symm

section Pullback

variable {ψ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ}

theorem hasCompactSupport_comp_toBall (hψ : HasCompactSupport ψ) :
    HasCompactSupport (fun p : CapSpace m => ψ (toBall m p)) := by
  have h := hψ.comp_homeomorph (toBallHomeo m)
  have hfun : (ψ ∘ (toBallHomeo m)) = fun p : CapSpace m => ψ (toBall m p) :=
    funext fun p => by rw [Function.comp_apply, toBallHomeo_apply]
  rwa [hfun] at h

theorem hasCompactSupport_comp_toBallNeg (hψ : HasCompactSupport ψ) :
    HasCompactSupport (fun p : CapSpace m => ψ (toBallNeg m p)) := by
  have h := hψ.comp_homeomorph (toBallNegHomeo m)
  have hfun : (ψ ∘ (toBallNegHomeo m)) = fun p : CapSpace m => ψ (toBallNeg m p) :=
    funext fun p => by rw [Function.comp_apply, toBallNegHomeo_apply]
  rwa [hfun] at h

theorem tsupport_comp_toBall
    (hψs : tsupport ψ ⊆ ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    tsupport (fun p : CapSpace m => ψ (toBall m p)) ⊆ capQ m := by
  have h1 : tsupport (fun p : CapSpace m => ψ (toBall m p)) ⊆ toBall m ⁻¹' (tsupport ψ) := by
    have hsupp : Function.support (fun p : CapSpace m => ψ (toBall m p))
        = toBall m ⁻¹' (Function.support ψ) := rfl
    rw [tsupport, hsupp]
    exact contDiff_toBall.continuous.closure_preimage_subset _
  refine h1.trans ?_
  rw [← toBall_preimage_ball]
  exact Set.preimage_mono hψs

theorem tsupport_comp_toBallNeg
    (hψs : tsupport ψ ⊆ ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    tsupport (fun p : CapSpace m => ψ (toBallNeg m p)) ⊆ capQ m := by
  have h1 : tsupport (fun p : CapSpace m => ψ (toBallNeg m p))
      ⊆ toBallNeg m ⁻¹' (tsupport ψ) := by
    have hsupp : Function.support (fun p : CapSpace m => ψ (toBallNeg m p))
        = toBallNeg m ⁻¹' (Function.support ψ) := rfl
    rw [tsupport, hsupp]
    exact contDiff_toBallNeg.continuous.closure_preimage_subset _
  refine h1.trans ?_
  rw [← toBallNeg_preimage_ball]
  exact Set.preimage_mono hψs

theorem integrableOn_mul_cont_rf {v : CapSpace m → ℝ}
    (hv : MemLp v 2 (volume.restrict ((Cap.hemisphere m).body))) {c : CapSpace m → ℝ}
    (hc : Continuous c) (hcc : HasCompactSupport c) :
    IntegrableOn (fun p => v p * c p) ((Cap.hemisphere m).body) :=
  hv.integrable_mul (Continuous.memLp_of_hasCompactSupport (p := 2) hc hcc)

end Pullback

/-! ### The reflected weak-gradient identity -/

set_option maxHeartbeats 1000000 in
theorem setIntegral_ball_deriv_split (u : H1P ((Cap.hemisphere m).body))
    {φ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (j : Fin (m + 1)) :
    (∫ x in ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1,
        reflectEvenFun u.toFun x * fderiv ℝ φ x (EuclideanSpace.single j (1:ℝ)))
      = (∫ p in (Cap.hemisphere m).body,
          u.toFun p * fderiv ℝ φ (toBall m p) (EuclideanSpace.single j (1:ℝ)))
        + ∫ p in (Cap.hemisphere m).body,
          u.toFun p * fderiv ℝ φ (toBallNeg m p) (EuclideanSpace.single j (1:ℝ)) := by
  have hcont : Continuous fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
      fderiv ℝ φ x (EuclideanSpace.single j (1:ℝ)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcs : HasCompactSupport fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
      fderiv ℝ φ x (EuclideanSpace.single j (1:ℝ)) := hφc.fderiv_apply ℝ _
  refine setIntegral_ball_of_halves_rf
    (integrableOn_mul_cont_rf u.memL2 (hcont.comp contDiff_toBall.continuous)
      (hasCompactSupport_comp_toBall hcs))
    (integrableOn_mul_cont_rf u.memL2 (hcont.comp contDiff_toBallNeg.continuous)
      (hasCompactSupport_comp_toBallNeg hcs)) (fun x hx => ?_) (fun x hx => ?_)
  · show reflectEvenFun u.toFun x * fderiv ℝ φ x (EuclideanSpace.single j (1:ℝ))
      = u.toFun (ofBall m x) * fderiv ℝ φ (toBall m (ofBall m x)) (EuclideanSpace.single j (1:ℝ))
    rw [toBall_ofBall, reflectEvenFun_eqOn_upper u.toFun hx]
  · show reflectEvenFun u.toFun x * fderiv ℝ φ x (EuclideanSpace.single j (1:ℝ))
      = u.toFun (ofBallNeg m x)
        * fderiv ℝ φ (toBallNeg m (ofBallNeg m x)) (EuclideanSpace.single j (1:ℝ))
    rw [toBallNeg_ofBallNeg, reflectEvenFun_eqOn_lower u.toFun hx]

theorem setIntegral_ball_grad_split_zero (u : H1P ((Cap.hemisphere m).body))
    {φ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) :
    (∫ x in ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1,
        reflectEvenGrad u.gx u.gz x 0 * φ x)
      = (∫ p in (Cap.hemisphere m).body, u.gx p * φ (toBall m p))
        + ∫ p in (Cap.hemisphere m).body, -u.gx p * φ (toBallNeg m p) := by
  refine setIntegral_ball_of_halves_rf
    (integrableOn_mul_cont_rf u.gx_memL2 (hφ.continuous.comp contDiff_toBall.continuous)
      (hasCompactSupport_comp_toBall hφc))
    (integrableOn_mul_cont_rf u.gx_memL2.neg (hφ.continuous.comp contDiff_toBallNeg.continuous)
      (hasCompactSupport_comp_toBallNeg hφc)) (fun x hx => ?_) (fun x hx => ?_)
  · show reflectEvenGrad u.gx u.gz x 0 * φ x
      = u.gx (ofBall m x) * φ (toBall m (ofBall m x))
    rw [toBall_ofBall, reflectEvenGrad_eqOn_upper u.gx u.gz hx]
    rfl
  · show reflectEvenGrad u.gx u.gz x 0 * φ x
      = -u.gx (ofBallNeg m x) * φ (toBallNeg m (ofBallNeg m x))
    rw [toBallNeg_ofBallNeg, reflectEvenGrad_eqOn_lower u.gx u.gz hx]
    rfl

theorem setIntegral_ball_grad_split_succ (u : H1P ((Cap.hemisphere m).body))
    {φ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (i : Fin m) :
    (∫ x in ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1,
        reflectEvenGrad u.gx u.gz x i.succ * φ x)
      = (∫ p in (Cap.hemisphere m).body, u.gz p i * φ (toBall m p))
        + ∫ p in (Cap.hemisphere m).body, u.gz p i * φ (toBallNeg m p) := by
  refine setIntegral_ball_of_halves_rf
    (integrableOn_mul_cont_rf (memLp_two_compP u.gz_memL2 i)
      (hφ.continuous.comp contDiff_toBall.continuous) (hasCompactSupport_comp_toBall hφc))
    (integrableOn_mul_cont_rf (memLp_two_compP u.gz_memL2 i)
      (hφ.continuous.comp contDiff_toBallNeg.continuous)
      (hasCompactSupport_comp_toBallNeg hφc)) (fun x hx => ?_) (fun x hx => ?_)
  · show reflectEvenGrad u.gx u.gz x i.succ * φ x
      = u.gz (ofBall m x) i * φ (toBall m (ofBall m x))
    rw [toBall_ofBall, reflectEvenGrad_eqOn_upper u.gx u.gz hx]
    rfl
  · show reflectEvenGrad u.gx u.gz x i.succ * φ x
      = u.gz (ofBallNeg m x) i * φ (toBallNeg m (ofBallNeg m x))
    rw [toBallNeg_ofBallNeg, reflectEvenGrad_eqOn_lower u.gx u.gz hx]
    rfl

theorem support_sub_subset_rf (f g : CapSpace m → ℝ) :
    Function.support (fun q => f q - g q) ⊆ Function.support f ∪ Function.support g := by
  intro q hq
  by_contra hcon
  simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hcon
  exact hq (by show f q - g q = 0; rw [hcon.1, hcon.2, sub_zero])

theorem support_add_subset_rf (f g : CapSpace m → ℝ) :
    Function.support (fun q => f q + g q) ⊆ Function.support f ∪ Function.support g := by
  intro q hq
  by_contra hcon
  simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hcon
  exact hq (by show f q + g q = 0; rw [hcon.1, hcon.2, add_zero])

variable {φ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ}

theorem fderiv_pullback_zero (hφ : ContDiff ℝ ∞ φ) (p : CapSpace m) :
    fderiv ℝ (fun q : CapSpace m => φ (toBall m q) - φ (toBallNeg m q)) p
        ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m)))
      = fderiv ℝ φ (toBall m p) (EuclideanSpace.single (0 : Fin (m + 1)) (1:ℝ))
        + fderiv ℝ φ (toBallNeg m p) (EuclideanSpace.single (0 : Fin (m + 1)) (1:ℝ)) := by
  have hd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have h1 : HasFDerivAt (fun q : CapSpace m => φ (toBall m q))
      ((fderiv ℝ φ (toBall m p)).comp (toEuclidL m)) p :=
    (hd (toBall m p)).hasFDerivAt.comp p (hasFDerivAt_toBall p)
  have h2 : HasFDerivAt (fun q : CapSpace m => φ (toBallNeg m q))
      ((fderiv ℝ φ (toBallNeg m p)).comp ((toEuclidL m).comp (negFstL m))) p :=
    (hd (toBallNeg m p)).hasFDerivAt.comp p (hasFDerivAt_toBallNeg p)
  have h3 : HasFDerivAt (fun q : CapSpace m => φ (toBall m q) - φ (toBallNeg m q))
      ((fderiv ℝ φ (toBall m p)).comp (toEuclidL m)
        - (fderiv ℝ φ (toBallNeg m p)).comp ((toEuclidL m).comp (negFstL m))) p := h1.sub h2
  rw [h3.fderiv]
  show fderiv ℝ φ (toBall m p) (toEuclid m ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))))
      - fderiv ℝ φ (toBallNeg m p) (toEuclid m (-(1 : ℝ), (0 : EuclideanSpace ℝ (Fin m)))) = _
  rw [toEuclid_one_zero, toEuclid_neg_one_zero, map_neg]
  ring

theorem fderiv_pullback_succ (hφ : ContDiff ℝ ∞ φ) (p : CapSpace m) (i : Fin m) :
    fderiv ℝ (fun q : CapSpace m => φ (toBall m q) + φ (toBallNeg m q)) p
        ((0 : ℝ), EuclideanSpace.single i (1:ℝ))
      = fderiv ℝ φ (toBall m p) (EuclideanSpace.single i.succ (1:ℝ))
        + fderiv ℝ φ (toBallNeg m p) (EuclideanSpace.single i.succ (1:ℝ)) := by
  have hd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have h1 : HasFDerivAt (fun q : CapSpace m => φ (toBall m q))
      ((fderiv ℝ φ (toBall m p)).comp (toEuclidL m)) p :=
    (hd (toBall m p)).hasFDerivAt.comp p (hasFDerivAt_toBall p)
  have h2 : HasFDerivAt (fun q : CapSpace m => φ (toBallNeg m q))
      ((fderiv ℝ φ (toBallNeg m p)).comp ((toEuclidL m).comp (negFstL m))) p :=
    (hd (toBallNeg m p)).hasFDerivAt.comp p (hasFDerivAt_toBallNeg p)
  have h3 : HasFDerivAt (fun q : CapSpace m => φ (toBall m q) + φ (toBallNeg m q))
      ((fderiv ℝ φ (toBall m p)).comp (toEuclidL m)
        + (fderiv ℝ φ (toBallNeg m p)).comp ((toEuclidL m).comp (negFstL m))) p := h1.add h2
  rw [h3.fderiv]
  show fderiv ℝ φ (toBall m p) (toEuclid m ((0 : ℝ), EuclideanSpace.single i (1:ℝ)))
      + fderiv ℝ φ (toBallNeg m p)
        (toEuclid m (-(0 : ℝ), EuclideanSpace.single i (1:ℝ))) = _
  rw [neg_zero, toEuclid_single_succ]

set_option maxHeartbeats 4000000 in
/-- **The reflected pair is a weak gradient on the whole ball.**  This is the heart of
deliverable 1: on each half ball the identity is the weak-gradient identity of `u` for the
pulled-back test function, and the two halves combine into the *even* (transverse) resp. *odd*
(axial) symmetrisation of the test function; the odd symmetrisation vanishes on the entrance
face, which is what allows the cut-off argument of `weakGrad_axial_face`. -/
theorem reflectEven_hasWeakGrad (u : H1P ((Cap.hemisphere m).body)) :
    HasWeakGrad (ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) (reflectEvenFun u.toFun)
      (reflectEvenGrad u.gx u.gz) := by
  intro φ hφ hφc hφs j
  refine Fin.cases ?_ (fun i => ?_) j
  · -- axial direction
    have hΨ : ContDiff ℝ ∞ (fun q : CapSpace m => φ (toBall m q) - φ (toBallNeg m q)) :=
      (hφ.comp contDiff_toBall).sub (hφ.comp contDiff_toBallNeg)
    have hΨc : HasCompactSupport (fun q : CapSpace m => φ (toBall m q) - φ (toBallNeg m q)) :=
      (hasCompactSupport_comp_toBall hφc).sub (hasCompactSupport_comp_toBallNeg hφc)
    have hΨs : tsupport (fun q : CapSpace m => φ (toBall m q) - φ (toBallNeg m q)) ⊆ capQ m := by
      refine (closure_mono (support_sub_subset_rf _ _)).trans ?_
      rw [closure_union]
      exact Set.union_subset (tsupport_comp_toBall hφs) (tsupport_comp_toBallNeg hφs)
    have hface : ∀ z : EuclideanSpace ℝ (Fin m),
        (fun q : CapSpace m => φ (toBall m q) - φ (toBallNeg m q)) ((-1 : ℝ), z) = 0 := by
      intro z
      have h : toBall m ((-1 : ℝ), z) = toBallNeg m ((-1 : ℝ), z) := by
        show toEuclid m ((-1 : ℝ) + 1, z) = toEuclid m (-((-1 : ℝ) + 1), z)
        norm_num
      show φ (toBall m ((-1 : ℝ), z)) - φ (toBallNeg m ((-1 : ℝ), z)) = 0
      rw [h, sub_self]
    have hcont0 : Continuous fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
        fderiv ℝ φ x (EuclideanSpace.single (0 : Fin (m + 1)) (1:ℝ)) :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hcs0 : HasCompactSupport fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
        fderiv ℝ φ x (EuclideanSpace.single (0 : Fin (m + 1)) (1:ℝ)) := hφc.fderiv_apply ℝ _
    have hI1 : IntegrableOn (fun p => u.toFun p *
        fderiv ℝ φ (toBall m p) (EuclideanSpace.single (0 : Fin (m + 1)) (1:ℝ)))
        ((Cap.hemisphere m).body) :=
      integrableOn_mul_cont_rf u.memL2 (hcont0.comp contDiff_toBall.continuous)
        (hasCompactSupport_comp_toBall hcs0)
    have hI2 : IntegrableOn (fun p => u.toFun p *
        fderiv ℝ φ (toBallNeg m p) (EuclideanSpace.single (0 : Fin (m + 1)) (1:ℝ)))
        ((Cap.hemisphere m).body) :=
      integrableOn_mul_cont_rf u.memL2 (hcont0.comp contDiff_toBallNeg.continuous)
        (hasCompactSupport_comp_toBallNeg hcs0)
    have hJ1 : IntegrableOn (fun p => u.gx p * φ (toBall m p)) ((Cap.hemisphere m).body) :=
      integrableOn_mul_cont_rf u.gx_memL2 (hφ.continuous.comp contDiff_toBall.continuous)
        (hasCompactSupport_comp_toBall hφc)
    have hJ2 : IntegrableOn (fun p => -u.gx p * φ (toBallNeg m p)) ((Cap.hemisphere m).body) :=
      integrableOn_mul_cont_rf u.gx_memL2.neg
        (hφ.continuous.comp contDiff_toBallNeg.continuous) (hasCompactSupport_comp_toBallNeg hφc)
    rw [setIntegral_ball_deriv_split u hφ hφc 0, setIntegral_ball_grad_split_zero u hφ hφc]
    have hL : (∫ p in (Cap.hemisphere m).body, u.toFun p *
          fderiv ℝ φ (toBall m p) (EuclideanSpace.single (0 : Fin (m + 1)) (1:ℝ)))
        + (∫ p in (Cap.hemisphere m).body, u.toFun p *
          fderiv ℝ φ (toBallNeg m p) (EuclideanSpace.single (0 : Fin (m + 1)) (1:ℝ)))
        = ∫ p in (Cap.hemisphere m).body, u.toFun p *
          fderiv ℝ (fun q : CapSpace m => φ (toBall m q) - φ (toBallNeg m q)) p
            ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))) := by
      rw [← integral_add hI1 hI2]
      refine setIntegral_congr_fun measurableSet_body_rf fun p _ => ?_
      rw [fderiv_pullback_zero hφ p]
      ring
    have hR : (∫ p in (Cap.hemisphere m).body, u.gx p * φ (toBall m p))
        + (∫ p in (Cap.hemisphere m).body, -u.gx p * φ (toBallNeg m p))
        = ∫ p in (Cap.hemisphere m).body,
          u.gx p * (φ (toBall m p) - φ (toBallNeg m p)) := by
      rw [← integral_add hJ1 hJ2]
      refine setIntegral_congr_fun measurableSet_body_rf fun p _ => ?_
      show u.gx p * φ (toBall m p) + -u.gx p * φ (toBallNeg m p) = _
      ring
    rw [hL, hR]
    exact weakGrad_axial_face u hΨ hΨc hΨs hface
  · -- transverse directions
    have hΨ : ContDiff ℝ ∞ (fun q : CapSpace m => φ (toBall m q) + φ (toBallNeg m q)) :=
      (hφ.comp contDiff_toBall).add (hφ.comp contDiff_toBallNeg)
    have hΨc : HasCompactSupport (fun q : CapSpace m => φ (toBall m q) + φ (toBallNeg m q)) :=
      (hasCompactSupport_comp_toBall hφc).add (hasCompactSupport_comp_toBallNeg hφc)
    have hΨs : tsupport (fun q : CapSpace m => φ (toBall m q) + φ (toBallNeg m q)) ⊆ capQ m := by
      refine (closure_mono (support_add_subset_rf _ _)).trans ?_
      rw [closure_union]
      exact Set.union_subset (tsupport_comp_toBall hφs) (tsupport_comp_toBallNeg hφs)
    have hconti : Continuous fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
        fderiv ℝ φ x (EuclideanSpace.single i.succ (1:ℝ)) :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hcsi : HasCompactSupport fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
        fderiv ℝ φ x (EuclideanSpace.single i.succ (1:ℝ)) := hφc.fderiv_apply ℝ _
    have hI1 : IntegrableOn (fun p => u.toFun p *
        fderiv ℝ φ (toBall m p) (EuclideanSpace.single i.succ (1:ℝ)))
        ((Cap.hemisphere m).body) :=
      integrableOn_mul_cont_rf u.memL2 (hconti.comp contDiff_toBall.continuous)
        (hasCompactSupport_comp_toBall hcsi)
    have hI2 : IntegrableOn (fun p => u.toFun p *
        fderiv ℝ φ (toBallNeg m p) (EuclideanSpace.single i.succ (1:ℝ)))
        ((Cap.hemisphere m).body) :=
      integrableOn_mul_cont_rf u.memL2 (hconti.comp contDiff_toBallNeg.continuous)
        (hasCompactSupport_comp_toBallNeg hcsi)
    have hJ1 : IntegrableOn (fun p => u.gz p i * φ (toBall m p)) ((Cap.hemisphere m).body) :=
      integrableOn_mul_cont_rf (memLp_two_compP u.gz_memL2 i)
        (hφ.continuous.comp contDiff_toBall.continuous) (hasCompactSupport_comp_toBall hφc)
    have hJ2 : IntegrableOn (fun p => u.gz p i * φ (toBallNeg m p)) ((Cap.hemisphere m).body) :=
      integrableOn_mul_cont_rf (memLp_two_compP u.gz_memL2 i)
        (hφ.continuous.comp contDiff_toBallNeg.continuous)
        (hasCompactSupport_comp_toBallNeg hφc)
    rw [setIntegral_ball_deriv_split u hφ hφc i.succ, setIntegral_ball_grad_split_succ u hφ hφc i]
    have hL : (∫ p in (Cap.hemisphere m).body, u.toFun p *
          fderiv ℝ φ (toBall m p) (EuclideanSpace.single i.succ (1:ℝ)))
        + (∫ p in (Cap.hemisphere m).body, u.toFun p *
          fderiv ℝ φ (toBallNeg m p) (EuclideanSpace.single i.succ (1:ℝ)))
        = ∫ p in (Cap.hemisphere m).body, u.toFun p *
          fderiv ℝ (fun q : CapSpace m => φ (toBall m q) + φ (toBallNeg m q)) p
            ((0 : ℝ), EuclideanSpace.single i (1:ℝ)) := by
      rw [← integral_add hI1 hI2]
      refine setIntegral_congr_fun measurableSet_body_rf fun p _ => ?_
      rw [fderiv_pullback_succ hφ p i]
      ring
    have hR : (∫ p in (Cap.hemisphere m).body, u.gz p i * φ (toBall m p))
        + (∫ p in (Cap.hemisphere m).body, u.gz p i * φ (toBallNeg m p))
        = ∫ p in (Cap.hemisphere m).body,
          u.gz p i * (φ (toBall m p) + φ (toBallNeg m p)) := by
      rw [← integral_add hJ1 hJ2]
      refine setIntegral_congr_fun measurableSet_body_rf fun p _ => ?_
      show u.gz p i * φ (toBall m p) + u.gz p i * φ (toBallNeg m p) = _
      ring
    rw [hL, hR]
    exact weakGrad_transverse_face u hΨ hΨc hΨs i

/-- **Deliverable 1: the even reflection** of a weak-`H¹` function of the hemispherical cap
body, as a weak-`H¹` function of the unit ball of `ℝ^{m+1}`. -/
def reflectEven (u : H1P ((Cap.hemisphere m).body)) :
    H1 (ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) where
  toFun := reflectEvenFun u.toFun
  grad := reflectEvenGrad u.gx u.gz
  memL2 := memLp_ball_of_halves_rf u.memL2 u.memL2 (reflectEvenFun_eqOn_upper u.toFun)
    (reflectEvenFun_eqOn_lower u.toFun)
  grad_memL2 := memLp_ball_of_halves_rf (memLp_gradPair u.gx_memL2 u.gz_memL2)
    (memLp_gradPair u.gx_memL2.neg u.gz_memL2) (reflectEvenGrad_eqOn_upper u.gx u.gz)
    (reflectEvenGrad_eqOn_lower u.gx u.gz)
  hasWeakGrad := reflectEven_hasWeakGrad u

@[simp] theorem reflectEven_toFun (u : H1P ((Cap.hemisphere m).body)) :
    (reflectEven u).toFun = reflectEvenFun u.toFun := rfl

@[simp] theorem reflectEven_grad (u : H1P ((Cap.hemisphere m).body)) :
    (reflectEven u).grad = reflectEvenGrad u.gx u.gz := rfl

/-! ### The energies double -/

/-- **The mass doubles under the even reflection.** -/
theorem mass_reflectEven (u : H1P ((Cap.hemisphere m).body)) :
    mass (reflectEven u) = 2 * massP u := by
  have hint : IntegrableOn (fun p => u.toFun p ^ 2) ((Cap.hemisphere m).body) :=
    u.memL2.integrable_sq
  have h := setIntegral_ball_of_halves_rf
    (F := fun x : EuclideanSpace ℝ (Fin (m + 1)) => reflectEvenFun u.toFun x ^ 2)
    (f := fun p => u.toFun p ^ 2) (g := fun p => u.toFun p ^ 2) hint hint
    (fun x hx => by
      show reflectEvenFun u.toFun x ^ 2 = u.toFun (ofBall m x) ^ 2
      rw [reflectEvenFun_eqOn_upper u.toFun hx])
    (fun x hx => by
      show reflectEvenFun u.toFun x ^ 2 = u.toFun (ofBallNeg m x) ^ 2
      rw [reflectEvenFun_eqOn_lower u.toFun hx])
  show (∫ x in ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1, reflectEvenFun u.toFun x ^ 2) = _
  rw [h, massP]
  ring

/-- **The Dirichlet energy doubles under the even reflection.** -/
theorem dirichlet_reflectEven (u : H1P ((Cap.hemisphere m).body)) :
    dirichlet (reflectEven u) = 2 * dirichletP u := by
  have hint : IntegrableOn (fun p => u.gx p ^ 2 + ‖u.gz p‖ ^ 2) ((Cap.hemisphere m).body) :=
    u.gx_memL2.integrable_sq.add ((memLp_two_iff_integrable_sq_norm u.gz_memL2.1).1 u.gz_memL2)
  have h := setIntegral_ball_of_halves_rf
    (F := fun x : EuclideanSpace ℝ (Fin (m + 1)) => ‖reflectEvenGrad u.gx u.gz x‖ ^ 2)
    (f := fun p => u.gx p ^ 2 + ‖u.gz p‖ ^ 2) (g := fun p => u.gx p ^ 2 + ‖u.gz p‖ ^ 2)
    hint hint
    (fun x hx => by
      show ‖reflectEvenGrad u.gx u.gz x‖ ^ 2
        = u.gx (ofBall m x) ^ 2 + ‖u.gz (ofBall m x)‖ ^ 2
      rw [norm_reflectEvenGrad_sq, capPt_eq_ofBall hx.2.le])
    (fun x hx => by
      show ‖reflectEvenGrad u.gx u.gz x‖ ^ 2
        = u.gx (ofBallNeg m x) ^ 2 + ‖u.gz (ofBallNeg m x)‖ ^ 2
      rw [norm_reflectEvenGrad_sq, capPt_eq_ofBallNeg hx.2.le])
  show (∫ x in ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1,
    ‖reflectEvenGrad u.gx u.gz x‖ ^ 2) = _
  rw [h, dirichletP]
  ring

/-! ## Deliverable 2: the trace on the curved boundary `Γ` -/

theorem continuous_capPt : Continuous (capPt m) := by
  refine Continuous.prodMk ((continuous_coord_zero_rf.abs).sub continuous_const) ?_
  exact continuous_snd.comp ((capLinearEquiv m).symm.continuous)

/-- **The `Γ`-trace of a weak-`H¹` function of the hemispherical cap**: the sphere trace of its
even reflection, at radius `1`.  Only its values on the upper half sphere `{w | 0 < w 0}` are
meaningful (they are the values on the curved boundary `Γ`). -/
def gammaTrace (u : H1P ((Cap.hemisphere m).body)) (w : EuclideanSpace ℝ (Fin (m + 1))) : ℝ :=
  traceSphere 1 (reflectEvenFun u.toFun) (reflectEvenGrad u.gx u.gz) w

theorem gammaTrace_eq (u : H1P ((Cap.hemisphere m).body)) (w : EuclideanSpace ℝ (Fin (m + 1))) :
    gammaTrace u w = traceSphere 1 (reflectEven u).toFun (reflectEven u).grad w := rfl

/-- **The trace of a continuous function is its boundary restriction.**  For a continuous
representative and almost every direction `w`, the `Γ`-trace is the value of `u` at the point of
the closed cap body lying over `w`; on the upper half sphere this point is
`(w 0 - 1, w')`, i.e. exactly the boundary point of `Γ` in the direction `w`
(the convention of `capSphereFun`). -/
theorem gammaTrace_eq_of_continuous (u : H1P ((Cap.hemisphere m).body))
    (hcont : Continuous u.toFun) :
    ∀ᵐ w ∂(sphereMeasure (m + 1)),
      gammaTrace u ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1)))
        = u.toFun (capPt m ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1)))) := by
  have h := traceSphere_eq_of_continuous (m := m + 1) (by omega) one_pos (reflectEven u)
    (hcont.comp continuous_capPt)
  filter_upwards [h] with w hw
  rw [gammaTrace_eq, hw, one_smul]
  rfl

/-- On the upper half sphere the `Γ`-trace point is the boundary point `(w 0 - 1, w')`. -/
theorem capPt_eq_gamma_point {w : EuclideanSpace ℝ (Fin (m + 1))} (hw : 0 ≤ w 0) :
    capPt m w = (w 0 - 1, (ofEuclid m w).2) := capPt_eq_ofBall hw

/-- **Deliverable 2: the trace inequality on the curved boundary of the hemispherical cap.**
The constant is `2 · max (4 · 2^m) (2^m)`, the factor `2` coming from the doubling of both
energies under the even reflection and `2^m = ((1/2)^{(m+1)-1})⁻¹` from the radial weight at
radius `R = 1` in dimension `m + 1`. -/
theorem gammaTrace_sq_integral_le (u : H1P ((Cap.hemisphere m).body)) :
    (∫ w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1,
        (gammaTrace u (w : EuclideanSpace ℝ (Fin (m + 1)))) ^ 2 ∂(sphereMeasure (m + 1)))
      ≤ 2 * max (4 * 2 ^ m) (2 ^ m) * (massP u + dirichletP u) := by
  have h := traceSphere_sq_integral_le (m := m + 1) (by omega) one_pos (reflectEven u)
  rw [mass_reflectEven, dirichlet_reflectEven] at h
  have hpow : (((1 : ℝ) / 2) ^ (m + 1 - 1))⁻¹ = 2 ^ m := by
    simp [one_div]
  rw [hpow] at h
  have heq : max ((4 / (1:ℝ)) * (2:ℝ) ^ m) ((1:ℝ) * (2:ℝ) ^ m)
      = max (4 * 2 ^ m) ((2:ℝ) ^ m) := by norm_num
  rw [heq] at h
  calc (∫ w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1,
        (gammaTrace u (w : EuclideanSpace ℝ (Fin (m + 1)))) ^ 2 ∂(sphereMeasure (m + 1)))
      ≤ max (4 * 2 ^ m) ((2:ℝ) ^ m) * (2 * massP u + 2 * dirichletP u) := h
    _ = 2 * max (4 * 2 ^ m) ((2:ℝ) ^ m) * (massP u + dirichletP u) := by ring

/-! ## Deliverable 3: the bridge to the cap's revolution integral -/

/-- The `Γ`-trace as a function of the boundary point of the cap: `gammaTraceFun u (s,z)` is the
trace in the direction of the recentred point `(s+1, z)`. -/
def gammaTraceFun (u : H1P ((Cap.hemisphere m).body)) (p : CapSpace m) : ℝ :=
  gammaTrace u (toBall m p)

theorem measurableSet_upperSphere_rf :
    MeasurableSet {w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 |
      0 < ((w : EuclideanSpace ℝ (Fin (m + 1)))) 0} := by
  have hc : Continuous fun w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 =>
      ((w : EuclideanSpace ℝ (Fin (m + 1)))) 0 :=
    continuous_coord_zero_rf.comp continuous_subtype_val
  exact measurableSet_lt measurable_const hc.measurable

/-- The cap's boundary integrand of `(gammaTraceFun u)²` is the indicator of the upper half
sphere of the squared trace. -/
theorem capSphereFun_gammaTraceFun (u : H1P ((Cap.hemisphere m).body))
    (w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    capSphereFun m (fun p => (gammaTraceFun u p) ^ 2) w
      = Set.indicator {w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 |
          0 < ((w : EuclideanSpace ℝ (Fin (m + 1)))) 0}
          (fun w => (gammaTrace u ((w : EuclideanSpace ℝ (Fin (m + 1))))) ^ 2) w := by
  by_cases hw : w ∈ {w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 |
      0 < ((w : EuclideanSpace ℝ (Fin (m + 1)))) 0}
  · have hw' : 0 < ((w : EuclideanSpace ℝ (Fin (m + 1)))) 0 := hw
    rw [Set.indicator_of_mem hw]
    show (if 0 < ((w : EuclideanSpace ℝ (Fin (m + 1)))) 0 then
      (gammaTraceFun u (((w : EuclideanSpace ℝ (Fin (m + 1)))) 0 - 1,
        (ofEuclid m ((w : EuclideanSpace ℝ (Fin (m + 1))))).2)) ^ 2 else 0) = _
    rw [if_pos hw', gammaTraceFun]
    have hb : toBall m (((w : EuclideanSpace ℝ (Fin (m + 1)))) 0 - 1,
        (ofEuclid m ((w : EuclideanSpace ℝ (Fin (m + 1))))).2)
        = ((w : EuclideanSpace ℝ (Fin (m + 1)))) :=
      toBall_ofBall _
    rw [hb]
  · have hw' : ¬ (0 < ((w : EuclideanSpace ℝ (Fin (m + 1)))) 0) := hw
    rw [Set.indicator_of_notMem hw]
    show (if 0 < ((w : EuclideanSpace ℝ (Fin (m + 1)))) 0 then _ else (0:ℝ)) = 0
    rw [if_neg hw']

theorem integrable_capSphereFun_gammaTrace (u : H1P ((Cap.hemisphere m).body))
    (hG : Integrable (fun w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 =>
      (gammaTrace u ((w : EuclideanSpace ℝ (Fin (m + 1))))) ^ 2) (sphereMeasure (m + 1))) :
    Integrable (capSphereFun m (fun p => (gammaTraceFun u p) ^ 2)) (sphereMeasure (m + 1)) := by
  refine (hG.indicator measurableSet_upperSphere_rf).congr ?_
  exact Filter.Eventually.of_forall fun w => (capSphereFun_gammaTraceFun u w).symm

/-- **Deliverable 3: the `Γ`-trace inequality in the form used by the cap functional.**  The
left-hand side is the project's lateral boundary integral of the unit hemispherical end cap
(`capLateralIntegral`, the surface-of-revolution integral). -/
theorem capLateralIntegral_gammaTrace_sq_le (hm : 1 ≤ m) (u : H1P ((Cap.hemisphere m).body))
    (hG : Integrable (fun w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 =>
      (gammaTrace u ((w : EuclideanSpace ℝ (Fin (m + 1))))) ^ 2) (sphereMeasure (m + 1))) :
    capLateralIntegral (Cap.hemisphere m) (fun p => (gammaTraceFun u p) ^ 2)
      ≤ 2 * max (4 * 2 ^ m) (2 ^ m) * (massP u + dirichletP u) := by
  rw [capLateralIntegral_hemisphere_eq m hm _ (integrable_capSphereFun_gammaTrace u hG)]
  refine le_trans (integral_mono (integrable_capSphereFun_gammaTrace u hG) hG ?_)
    (gammaTrace_sq_integral_le u)
  intro w
  rw [capSphereFun_gammaTraceFun u w]
  by_cases hw : w ∈ {w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 |
      0 < ((w : EuclideanSpace ℝ (Fin (m + 1)))) 0}
  · rw [Set.indicator_of_mem hw]
  · rw [Set.indicator_of_notMem hw]
    positivity

/-- For a continuous representative the squared trace is integrable on the sphere, so the
hypothesis of `capLateralIntegral_gammaTrace_sq_le` is automatic. -/
theorem integrable_gammaTrace_sq_of_continuous (u : H1P ((Cap.hemisphere m).body))
    (hcont : Continuous u.toFun) :
    Integrable (fun w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 =>
      (gammaTrace u ((w : EuclideanSpace ℝ (Fin (m + 1))))) ^ 2) (sphereMeasure (m + 1)) := by
  have hc : Continuous fun w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 =>
      (u.toFun (capPt m ((w : EuclideanSpace ℝ (Fin (m + 1)))))) ^ 2 :=
    ((hcont.comp continuous_capPt).comp continuous_subtype_val).pow 2
  have hcpt : IsCompact (Set.univ : Set (sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)) :=
    isCompact_univ
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hc.continuousOn
  have hint : Integrable (fun w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 =>
      (u.toFun (capPt m ((w : EuclideanSpace ℝ (Fin (m + 1)))))) ^ 2) (sphereMeasure (m + 1)) := by
    refine Integrable.mono' (integrable_const C) hc.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun w => hC w (Set.mem_univ w)
  refine hint.congr ?_
  filter_upwards [gammaTrace_eq_of_continuous u hcont] with w hw
  rw [hw]

/-! ## Deliverable 4: linearity of the trace -/

section Linearity

variable {n : ℕ} {R : ℝ}

/-- **Additivity of the sphere trace** (almost everywhere).  Proved from the uniqueness of the
constant in `traceSphere_eq_const_add`. -/
theorem traceSphere_add_rf (hn : 1 ≤ n) (hR : 0 < R)
    (u v s : H1 (ball (0 : EuclideanSpace ℝ (Fin n)) R))
    (hs : ∀ x, s.toFun x = u.toFun x + v.toFun x)
    (hsg : ∀ x, s.grad x = u.grad x + v.grad x) :
    ∀ᵐ w ∂(sphereMeasure n),
      traceSphere R s.toFun s.grad ((w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
          EuclideanSpace ℝ (Fin n))
        = traceSphere R u.toFun u.grad ((w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
            EuclideanSpace ℝ (Fin n))
          + traceSphere R v.toFun v.grad ((w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
            EuclideanSpace ℝ (Fin n)) := by
  have hhalf : R / 2 ∈ Set.Ioo (0:ℝ) R := ⟨by linarith, by linarith⟩
  have hmid : ((R / 2 + R) / 2) ∈ Set.Ioo (R / 2) R := ⟨by linarith, by linarith⟩
  filter_upwards [traceSphere_eq_const_add hn hR u, traceSphere_eq_const_add hn hR v,
    traceSphere_eq_const_add hn hR s, ae_integrableOn_slice_inner (R := R) hn u.grad_memL2,
    ae_integrableOn_slice_inner (R := R) hn v.grad_memL2] with w hu hv hs' hiu hiv
  obtain ⟨cu, hcu, htu⟩ := hu
  obtain ⟨cv, hcv, htv⟩ := hv
  obtain ⟨cs, hcs, hts⟩ := hs'
  set wv : EuclideanSpace ℝ (Fin n) :=
    ((w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : EuclideanSpace ℝ (Fin n)) with hwv
  set Fu : ℝ → ℝ := fun t => inner ℝ (u.grad (t • wv)) wv with hFu
  set Fv : ℝ → ℝ := fun t => inner ℝ (v.grad (t • wv)) wv with hFv
  -- the slices of the gradients are interval integrable on every `[c, r] ⊆ (R/2, R)`
  have hIu : IntegrableOn Fu (Set.Ioo (R / 2) R) := (hiu _ hhalf).1
  have hIv : IntegrableOn Fv (Set.Ioo (R / 2) R) := (hiv _ hhalf).1
  have hint : ∀ (F : ℝ → ℝ), IntegrableOn F (Set.Ioo (R / 2) R) → ∀ r ∈ Set.Ioo (R / 2) R,
      IntervalIntegrable F volume ((R / 2 + R) / 2) r := by
    intro F hF r hr
    refine intervalIntegrable_iff.2 (hF.mono_set ?_)
    intro t ht
    have h1 : min ((R / 2 + R) / 2) r < t := lt_of_le_of_lt (le_refl _) ht.1
    constructor
    · exact lt_of_le_of_lt (le_min hmid.1.le hr.1.le) h1
    · exact lt_of_le_of_lt ht.2 (max_lt hmid.2 hr.2)
  have hintR : ∀ (F : ℝ → ℝ), IntegrableOn F (Set.Ioo (R / 2) R) →
      IntervalIntegrable F volume ((R / 2 + R) / 2) R := by
    intro F hF
    refine intervalIntegrable_iff.2 ?_
    have huIoc : Set.uIoc ((R / 2 + R) / 2) R = Set.Ioc ((R / 2 + R) / 2) R := by
      rw [Set.uIoc_of_le hmid.2.le]
    rw [huIoc, integrableOn_Ioc_iff_integrableOn_Ioo]
    refine (hF.mono_set ?_)
    intro t ht
    exact ⟨lt_trans hmid.1 ht.1, ht.2⟩
  -- the constants add
  have hsum : cs = cu + cv := by
    have hmeas : (volume.restrict (Set.Ioo (R / 2) R)) ≠ 0 := by
      intro hzero
      have hpos : volume (Set.Ioo (R / 2) R) ≠ 0 := by
        rw [Real.volume_Ioo]
        simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        linarith
      exact hpos (by simpa [Measure.restrict_apply_univ] using congrArg (fun μ => μ Set.univ) hzero)
    haveI : (ae (volume.restrict (Set.Ioo (R / 2) R))).NeBot := ae_neBot.2 hmeas
    have hcomb : ∀ᵐ r ∂(volume.restrict (Set.Ioo (R / 2) R)), cs = cu + cv := by
      filter_upwards [hcu, hcv, hcs, ae_restrict_mem measurableSet_Ioo] with r h1 h2 h3 hr
      have hJ : (∫ t in ((R / 2 + R) / 2)..r, inner ℝ (s.grad (t • wv)) wv)
          = (∫ t in ((R / 2 + R) / 2)..r, Fu t) + ∫ t in ((R / 2 + R) / 2)..r, Fv t := by
        rw [← intervalIntegral.integral_add (hint Fu hIu r hr) (hint Fv hIv r hr)]
        refine intervalIntegral.integral_congr (fun t _ => ?_)
        show inner ℝ (s.grad (t • wv)) wv = Fu t + Fv t
        rw [hsg (t • wv), hFu, hFv]
        simp [inner_add_left]
      have h4 : s.toFun (r • wv) = u.toFun (r • wv) + v.toFun (r • wv) := hs _
      rw [h3, hJ] at h4
      rw [h1, h2] at h4
      linarith
    exact hcomb.exists.choose_spec
  have hJR : (∫ t in ((R / 2 + R) / 2)..R, inner ℝ (s.grad (t • wv)) wv)
      = (∫ t in ((R / 2 + R) / 2)..R, Fu t) + ∫ t in ((R / 2 + R) / 2)..R, Fv t := by
    rw [← intervalIntegral.integral_add (hintR Fu hIu) (hintR Fv hIv)]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    show inner ℝ (s.grad (t • wv)) wv = Fu t + Fv t
    rw [hsg (t • wv), hFu, hFv]
    simp [inner_add_left]
  rw [hts, htu, htv, hJR, hsum]
  ring

/-- **Homogeneity of the sphere trace.** -/
theorem traceSphere_smul_rf (R c : ℝ) (U : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (wv : EuclideanSpace ℝ (Fin n)) :
    traceSphere R (fun x => c * U x) (fun x => c • G x) wv = c * traceSphere R U G wv := by
  have hJ : ∀ r : ℝ, (∫ t in ((R / 2 + R) / 2)..r, inner ℝ (c • G (t • wv)) wv)
      = c * ∫ t in ((R / 2 + R) / 2)..r, inner ℝ (G (t • wv)) wv := by
    intro r
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun t _ => real_inner_smul_left _ _ _)
  simp only [traceSphere, hJ]
  have hOut : (∫ r in Set.Ioo (R / 2) R, (c * U (r • wv)
        - c * ∫ t in ((R / 2 + R) / 2)..r, inner ℝ (G (t • wv)) wv))
      = c * ∫ r in Set.Ioo (R / 2) R, (U (r • wv)
        - ∫ t in ((R / 2 + R) / 2)..r, inner ℝ (G (t • wv)) wv) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioo fun r _ => by ring
  rw [hOut]
  ring

end Linearity

/-- The even reflection is additive. -/
theorem reflectEven_grad_add (u v : H1P ((Cap.hemisphere m).body))
    (x : EuclideanSpace ℝ (Fin (m + 1))) :
    (reflectEven (u + v)).grad x = (reflectEven u).grad x + (reflectEven v).grad x := by
  show toEuclid m (sgn0 x * (u.gx (capPt m x) + v.gx (capPt m x)),
      u.gz (capPt m x) + v.gz (capPt m x))
    = toEuclid m (sgn0 x * u.gx (capPt m x), u.gz (capPt m x))
      + toEuclid m (sgn0 x * v.gx (capPt m x), v.gz (capPt m x))
  rw [← toEuclid_add_rf]
  congr 1
  refine Prod.ext ?_ rfl
  show sgn0 x * (u.gx (capPt m x) + v.gx (capPt m x))
    = sgn0 x * u.gx (capPt m x) + sgn0 x * v.gx (capPt m x)
  ring

/-- The even reflection is homogeneous. -/
theorem reflectEven_grad_smul (c : ℝ) (u : H1P ((Cap.hemisphere m).body))
    (x : EuclideanSpace ℝ (Fin (m + 1))) :
    (reflectEven (c • u)).grad x = c • (reflectEven u).grad x := by
  show toEuclid m (sgn0 x * (c * u.gx (capPt m x)), c • u.gz (capPt m x))
    = c • toEuclid m (sgn0 x * u.gx (capPt m x), u.gz (capPt m x))
  rw [← toEuclid_smul_rf]
  congr 1
  refine Prod.ext ?_ rfl
  show sgn0 x * (c * u.gx (capPt m x)) = c * (sgn0 x * u.gx (capPt m x))
  ring

/-- **Deliverable 4 (additivity).**  The `Γ`-trace is additive almost everywhere. -/
theorem gammaTrace_add (u v : H1P ((Cap.hemisphere m).body)) :
    ∀ᵐ w ∂(sphereMeasure (m + 1)),
      gammaTrace (u + v) ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1)))
        = gammaTrace u ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
            EuclideanSpace ℝ (Fin (m + 1)))
          + gammaTrace v ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
            EuclideanSpace ℝ (Fin (m + 1))) :=
  traceSphere_add_rf (n := m + 1) (by omega) one_pos (reflectEven u) (reflectEven v)
    (reflectEven (u + v)) (fun _ => rfl) (reflectEven_grad_add u v)

/-- **Deliverable 4 (homogeneity).**  The `Γ`-trace is homogeneous (everywhere). -/
theorem gammaTrace_smul (c : ℝ) (u : H1P ((Cap.hemisphere m).body))
    (w : EuclideanSpace ℝ (Fin (m + 1))) :
    gammaTrace (c • u) w = c * gammaTrace u w := by
  have hf : reflectEvenFun ((c • u).toFun)
      = fun x => c * reflectEvenFun u.toFun x := rfl
  have hg : reflectEvenGrad ((c • u).gx) ((c • u).gz)
      = fun x => c • reflectEvenGrad u.gx u.gz x := funext (reflectEven_grad_smul c u)
  show traceSphere 1 (reflectEvenFun ((c • u).toFun))
    (reflectEvenGrad ((c • u).gx) ((c • u).gz)) w = _
  rw [hf, hg, traceSphere_smul_rf]
  rfl

end

end RobinCaps.ThinDomain
