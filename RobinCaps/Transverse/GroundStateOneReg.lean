import RobinCaps.Transverse.GroundStateOneFull
import RobinCaps.ThinDomain.Trial
import RobinCaps.ThinDomain.Polar

/-!
# The regular transverse ground state for `m = 1`, and its boundary form on `S⁰`

This file upgrades the fully proved transverse ground state of
`RobinCaps/Transverse/GroundStateOneFull.lean` to the *regular* structure
`RobinCaps.ThinDomain.TransverseGroundStateReg` used by the trial-function construction of
`RobinCaps/ThinDomain/Trial.lean`, and identifies the trace boundary form `bdTr` with the
sphere integral of `RobinCaps/ThinDomain/Polar.lean` over `S⁰ = {±R}`.

* Part 1 — the two regularity fields for the normalised ground state `psiN`
  (`psiN_contDiff`, `psiN_grad_eq`);
* Part 2 — `groundStateOneReg`, the regular transverse ground state;
* Part 3 — the unit sphere of `EuclideanSpace ℝ (Fin 1)` is the two-point set
  `{ept 1, ept (-1)}` (`sphere_one_eq_pair`), `sphereMeasure 1` is the counting measure on
  these two points (`sphereMeasure_one_spPlus`, `sphereMeasure_one_spMinus`), hence
  `integral_sphere_one` and `sphereIntegral_one_eq`;
* Part 4 — `bdTr_eq_sphereIntegral` : for a continuous representative the trace boundary form
  is the sphere integral of the square, in particular for `psiN`
  (`bdTr_psiN_eq_sphereIntegral`).

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

namespace RobinCaps.Transverse

open MeasureTheory Set RobinCaps.Sobolev RobinCaps.ThinDomain

open scoped InnerProductSpace ENNReal ContDiff Pointwise

variable (α R : ℝ)

/-! ## Part 1. Regularity of the normalised ground state `psiN` -/

/-- The normalising constant of `psiN` : `ψ_N = cNorm · ψ`. -/
def cNorm (hα : 0 < α) (hR : 0 < R) : ℝ :=
  (Real.sqrt (Weak.mass (psi1 α R hα hR)))⁻¹

theorem psiN_toFun_eq (hα : 0 < α) (hR : 0 < R) (z : EuclideanSpace ℝ (Fin 1)) :
    (psiN α R hα hR).toFun z = cNorm α R hα hR * psiFun α R hα hR z := rfl

/-- **`ψ_N` is `C¹`** : the `psiC1` field of `TransverseGroundStateReg`. -/
theorem psiN_contDiff (hα : 0 < α) (hR : 0 < R) :
    ContDiff ℝ 1 (fun z => (psiN α R hα hR).toFun z) := by
  have h : (fun z => (psiN α R hα hR).toFun z)
      = fun z => cNorm α R hα hR * psiFun α R hα hR z :=
    funext fun z => psiN_toFun_eq α R hα hR z
  rw [h]
  exact contDiff_const.mul (contDiff_psiFun α R hα hR)

/-- **The chosen weak gradient of `ψ_N` is its classical gradient** : the `grad_eq` field of
`TransverseGroundStateReg`. -/
theorem psiN_grad_eq (hα : 0 < α) (hR : 0 < R) :
    ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) R,
      (psiN α R hα hR).grad z
        = Weak.classicalGrad (fun w => (psiN α R hα hR).toFun w) z := by
  intro z _
  have hd : DifferentiableAt ℝ (psiFun α R hα hR) z :=
    ((contDiff_psiFun α R hα hR).differentiable le_rfl) z
  have hfun : (fun w => (psiN α R hα hR).toFun w)
      = fun w => cNorm α R hα hR * psiFun α R hα hR w :=
    funext fun w => psiN_toFun_eq α R hα hR w
  ext i
  have hL : (psiN α R hα hR).grad z i
      = cNorm α R hα hR * fderiv ℝ (psiFun α R hα hR) z (EuclideanSpace.single i 1) := rfl
  rw [hL, hfun, Weak.classicalGrad_apply, fderiv_const_mul hd]
  simp

/-! ## Part 2. The regular transverse ground state -/

/-- **The regular transverse ground state in transverse dimension `m = 1`** : the ground state
`groundStateOne` of `RobinCaps/Transverse/GroundStateOneFull.lean` together with the two
regularity fields required by the trial-function construction. -/
def groundStateOneReg (α R : ℝ) (hα : 0 < α) (hR : 0 < R) :
    ThinDomain.TransverseGroundStateReg 1 α R (bdTr R) where
  toTransverseGroundState := groundStateOne α R hα hR
  psiC1 := psiN_contDiff α R hα hR
  grad_eq := psiN_grad_eq α R hα hR

@[simp] theorem groundStateOneReg_psi (hα : 0 < α) (hR : 0 < R) :
    (groundStateOneReg α R hα hR).psi = psiN α R hα hR := rfl

@[simp] theorem groundStateOneReg_nu (hα : 0 < α) (hR : 0 < R) :
    (groundStateOneReg α R hα hR).nu = nuR α R hα hR := rfl

/-! ## Part 3. The zero-dimensional sphere `S⁰` -/

/-- Every point of `EuclideanSpace ℝ (Fin 1)` is `ept` of its unique coordinate. -/
theorem eq_ept (z : EuclideanSpace ℝ (Fin 1)) : z = ept (z 0) := by
  ext i
  fin_cases i
  rfl

/-- **The unit sphere of `EuclideanSpace ℝ (Fin 1)` is the two-point set `{±1}`.** -/
theorem sphere_one_eq_pair :
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 : Set (EuclideanSpace ℝ (Fin 1)))
      = {ept 1, ept (-1)} := by
  ext z
  constructor
  · intro hz
    have hn : ‖z‖ = 1 := by simpa using mem_sphere_zero_iff_norm.1 hz
    have h2 : (z 0) ^ 2 = 1 := by rw [← norm_sq_one_dim, hn]; norm_num
    have h3 : (z 0 - 1) * (z 0 + 1) = 0 := by nlinarith
    rcases mul_eq_zero.1 h3 with h | h
    · left
      have : z 0 = 1 := by linarith
      rw [eq_ept z, this]
    · right
      have : z 0 = -1 := by linarith
      rw [eq_ept z, this]
      simp
  · intro hz
    rcases hz with h | h
    · rw [h]
      simp [ept_norm]
    · rw [show z = ept (-1) from h]
      simp [ept_norm]

/-- The point `+1` of `S⁰`. -/
def spPlus : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 :=
  ⟨ept 1, by simp [ept_norm]⟩

/-- The point `-1` of `S⁰`. -/
def spMinus : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 :=
  ⟨ept (-1), by simp [ept_norm]⟩

theorem spPlus_ne_spMinus : spPlus ≠ spMinus := by
  intro h
  have h0 : ept (1 : ℝ) = ept (-1 : ℝ) := congrArg Subtype.val h
  have h1 : (1 : ℝ) = -1 := congrArg (fun z : EuclideanSpace ℝ (Fin 1) => z 0) h0
  norm_num at h1

theorem sphere_one_mem_pair (w : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :
    w = spPlus ∨ w = spMinus := by
  have h : (w : EuclideanSpace ℝ (Fin 1)) ∈ ({ept 1, ept (-1)} :
      Set (EuclideanSpace ℝ (Fin 1))) := by
    rw [← sphere_one_eq_pair]; exact w.2
  rcases h with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

theorem finite_sphere_one :
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 : Set (EuclideanSpace ℝ (Fin 1))).Finite := by
  rw [sphere_one_eq_pair]
  exact (Set.finite_singleton _).insert _

instance instFiniteSphereOne :
    Finite (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
  finite_sphere_one.to_subtype

/-- The Lebesgue measure of an `ept`-image is the Lebesgue measure of the set. -/
theorem volume_ept_image (s : Set ℝ) :
    (volume : Measure (EuclideanSpace ℝ (Fin 1))) (ept '' s) = volume s := by
  have hemb : MeasurableEmbedding ept := eptEquiv.measurableEmbedding
  rw [← measurePreserving_ept.map_eq, hemb.map_apply,
    Set.preimage_image_eq _ hemb.injective]

theorem smul_image_ept_one :
    (Ioo (0 : ℝ) 1 • ({ept 1} : Set (EuclideanSpace ℝ (Fin 1)))) = ept '' Ioo (0 : ℝ) 1 := by
  rw [Set.smul_singleton]
  exact Set.image_congr fun r _ => (ept_eq_smul r).symm

theorem smul_image_ept_neg_one :
    (Ioo (0 : ℝ) 1 • ({ept (-1)} : Set (EuclideanSpace ℝ (Fin 1))))
      = ept '' Ioo (-1 : ℝ) 0 := by
  rw [Set.smul_singleton]
  ext z
  constructor
  · rintro ⟨r, hr, rfl⟩
    refine ⟨-r, ⟨by linarith [hr.2], by linarith [hr.1]⟩, ?_⟩
    show ept (-r) = r • ept (-1)
    rw [ept_eq_smul (-r), ept_eq_smul (-1 : ℝ), smul_smul]
    norm_num
  · rintro ⟨t, ht, rfl⟩
    refine ⟨-t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
    show (-t) • ept (-1) = ept t
    rw [ept_eq_smul t, ept_eq_smul (-1 : ℝ), smul_smul]
    norm_num

/-- **The mass of the point `+1` in `σ = volume.toSphere` is `1`.** -/
theorem sphereMeasure_one_spPlus : sphereMeasure 1 {spPlus} = 1 := by
  rw [Measure.toSphere_apply' _ (measurableSet_singleton _)]
  rw [Set.image_singleton]
  have hval : ((spPlus : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :
      EuclideanSpace ℝ (Fin 1)) = ept 1 := rfl
  rw [hval, smul_image_ept_one, volume_ept_image, Real.volume_Ioo,
    ThinDomain.finrank_eq 1]
  norm_num

/-- **The mass of the point `-1` in `σ = volume.toSphere` is `1`.** -/
theorem sphereMeasure_one_spMinus : sphereMeasure 1 {spMinus} = 1 := by
  rw [Measure.toSphere_apply' _ (measurableSet_singleton _)]
  rw [Set.image_singleton]
  have hval : ((spMinus : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :
      EuclideanSpace ℝ (Fin 1)) = ept (-1) := rfl
  rw [hval, smul_image_ept_neg_one, volume_ept_image, Real.volume_Ioo,
    ThinDomain.finrank_eq 1]
  norm_num

/-- **The surface measure of `S⁰` is the counting measure on `{±1}`** : integration against it
is the sum of the two endpoint values. -/
theorem integral_sphere_one (g : EuclideanSpace ℝ (Fin 1) → ℝ) :
    ∫ w : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1, g w ∂(sphereMeasure 1)
      = g (ept 1) + g (ept (-1)) := by
  classical
  have hint : Integrable (fun w : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 => g w)
      (sphereMeasure 1) := Integrable.of_finite
  rw [integral_countable' hint]
  rw [tsum_eq_sum (s := ({spPlus, spMinus} : Finset _))
    (fun b hb => absurd (by
      rcases sphere_one_mem_pair b with h | h <;> simp [h]) hb)]
  rw [Finset.sum_pair spPlus_ne_spMinus]
  have h1 : (sphereMeasure 1).real {spPlus} = 1 := by
    rw [measureReal_def, sphereMeasure_one_spPlus]; norm_num
  have h2 : (sphereMeasure 1).real {spMinus} = 1 := by
    rw [measureReal_def, sphereMeasure_one_spMinus]; norm_num
  rw [h1, h2]
  simp [spPlus, spMinus]

/-- **The sphere integral over `S⁰_R = {±R}`.**  (No hypothesis on `R` is needed: the weight
`R ^ (1 - 1) = R ^ 0` is `1`.) -/
theorem sphereIntegral_one_eq (R : ℝ) (g : EuclideanSpace ℝ (Fin 1) → ℝ) :
    sphereIntegral 1 R g = g (ept R) + g (ept (-R)) := by
  have hpow : (1 : ℕ) - 1 = 0 := rfl
  rw [sphereIntegral, hpow, pow_zero, one_mul,
    integral_sphere_one (fun z => g (R • z))]
  have e1 : R • ept (1 : ℝ) = ept R := (ept_eq_smul R).symm
  have e2 : R • ept (-1 : ℝ) = ept (-R) := by
    rw [ept_eq_smul (-1 : ℝ), ept_eq_smul (-R), smul_smul]
    norm_num
  rw [e1, e2]

/-! ## Part 4. The trace boundary form is the sphere integral of the square -/

/-- **Compatibility of the trace boundary form with the sphere integral**: for a continuous
representative `u`, `bdTr R u u = ∫_{S⁰_R} u²`. -/
theorem bdTr_eq_sphereIntegral {R : ℝ} (hR : 0 < R) (u : TransH1 1 R)
    (hu : Continuous u.toFun) :
    bdTr R u u = sphereIntegral 1 R (fun z => u.toFun z ^ 2) := by
  rw [bdTr_eq_bdPt_of_continuous hR u u hu hu, sphereIntegral_one_eq, bdPt]
  ring

/-- The boundary form of the transverse ground state as a sphere integral. -/
theorem bdTr_psiN_eq_sphereIntegral (hα : 0 < α) (hR : 0 < R) :
    bdTr R (psiN α R hα hR) (psiN α R hα hR)
      = sphereIntegral 1 R (fun z => (psiN α R hα hR).toFun z ^ 2) :=
  bdTr_eq_sphereIntegral hR _ (psiN_contDiff α R hα hR).continuous

end RobinCaps.Transverse

end
