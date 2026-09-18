import RobinCaps.Transverse.GroundStateOne
import RobinCaps.Sobolev.DuBoisReymond
import RobinCaps.Sobolev.PiconeGeneral
import RobinCaps.Transverse.OneDim

/-!
# The transverse Robin ground state in transverse dimension `m = 1`, completed

This file closes the three `Prop`-valued targets left open by
`RobinCaps/Transverse/GroundStateOne.lean` — `TraceOneTarget`, `GroundStateOneTarget` and
`GapFieldOneTarget` — and produces an actual instance of
`RobinCaps.ThinDomain.TransverseGroundState 1 α R (bdTr R)`.

## The bridge

For `m = 1` the transverse ball `B_1(R) ⊂ EuclideanSpace ℝ (Fin 1)` is the interval `(−R, R)`,
identified with `(0, 2R)` by the affine map `eptSh R : x ↦ ept (x − R)` (measure preserving,
a measurable embedding, with `eptSh R ⁻¹' B_1(R) = (0, 2R)`).

* **Part 1** (`hasWeakDeriv_slice`).  For `v ∈ H¹(B_1(R))` the slice `x ↦ v(ept (x − R))` has
  the coordinate `x ↦ (∇v)(ept (x − R))₀` of the weak gradient as a one-dimensional weak
  derivative on `(0, 2R)`.  The test functions `φ` of the interval model are transplanted to
  the ball by `liftTest R φ z = φ (z₀ + R)`, which is smooth, compactly supported inside the
  ball, and whose directional derivative along `e₀` is `φ'`.
* **Part 2** (`rep`).  The du Bois-Reymond bridge `Sobolev.exists_h1_of_hasWeakDeriv` turns this
  into an *absolutely continuous* representative `rep hR v : Sobolev.H1 (2R)` with
  `rep hR v =ᵐ slice v` and `deriv (rep hR v) =ᵐ` the gradient slice.  Two elements of
  `Sobolev.H1 ℓ` a.e. equal on `(0,ℓ)` are equal on the *closed* interval `[0,ℓ]`
  (`H1_eqOn_of_ae_eq`), so `rep` is unique on `[0, 2R]` and additive/homogeneous there.
* **Part 3** (`bdTr`).  The endpoint values `trZero`, `trEnd` of `rep` are therefore linear and
  a.e.-invariant, and `bdTr R u v = (Tr u)(−R)(Tr v)(−R) + (Tr u)(R)(Tr v)(R)` is an honest
  bilinear form: the one-dimensional **trace**.  It is symmetric (`bdTr_symm`), nonnegative
  (`bdTr_nonneg`), agrees with the pointwise endpoint form `bdPt` on continuous representatives
  (`bdTr_eq_bdPt_of_continuous`), and vanishes on null elements (`bdTr_vanishes`).
* **Part 4**.  `NBilin`, `dirichletBilin` and `qBilin α (bdTr R)` are the `L²`, Dirichlet and
  Robin forms of the representatives on `(0, 2R)` (`NBilin_eq_massBilin_rep`,
  `dirichletBilin_eq_rep`, `qBilin_eq_robinBilin_rep`).
* **Part 5** (`robinBilin_phaseEigen_left`).  The phase eigenfunction `e_j` is a weak
  eigenfunction against **every** `W ∈ H¹(0,ℓ)`: `a_{p,q;ℓ}(e_j, W) = μ_j ⟪e_j, W⟫`.  The proof
  is the integration by parts `RobinCaps.Transverse.ibp_lin`, which needs no differentiability
  of `W`, plus the two Robin boundary conditions.
* **Part 6** (`robinForm_ge_of_orth`).  If `W ⊥_{L²} e₁` then `μ₂ N[W] ≤ a[W]`.  This is the
  two-dimensional trial space `span {⟦e₁⟧, ⟦W⟧}` in the quotient `H1Q ℓ`: by Part 5 the pair is
  form-orthogonal, so the Rayleigh quotient on the span is `≤ max (μ₁, a[W]/N[W])`, and
  `robinMinmaxQ_eq_mu` together with `μ₁ < μ₂` forces `μ₂ ≤ a[W]/N[W]`.
* **Part 7**.  `groundStateOne α R hα hR : TransverseGroundState 1 α R (bdTr R)`, with
  `psi = psiN`, `nu = ν_R`, `gapConst = R² (λ₂ − ν_R) > 0`.  The quantitative small-`R` bound
  `gapConst ≥ c` is `groundStateOne_gap_quant`, from `transverse_gap_oneDim`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

namespace RobinCaps.Transverse

open MeasureTheory Set RobinCaps.Sobolev RobinCaps.ThinDomain

open scoped InnerProductSpace ENNReal ContDiff

/-! ## Part 0. The affine identification of `(0, 2R)` with the ball `(−R, R)` -/

/-- The affine identification `x ↦ ept (x − R)` of `(0, 2R)` with `B_1(R) = (−R, R)`. -/
def eptSh (R : ℝ) (x : ℝ) : EuclideanSpace ℝ (Fin 1) := ept (x - R)

@[simp] theorem eptSh_apply (R x : ℝ) (i : Fin 1) : eptSh R x i = x - R := rfl

@[simp] theorem coord_eptSh (R x : ℝ) : (eptSh R x) 0 + R = x := by
  simp

theorem eptSh_coord (R : ℝ) (z : EuclideanSpace ℝ (Fin 1)) : eptSh R (z 0 + R) = z := by
  ext i
  fin_cases i
  simp [eptSh]

theorem norm_one_dim (z : EuclideanSpace ℝ (Fin 1)) : ‖z‖ = |z 0| := by
  have h : ‖z‖ ^ 2 = |z 0| ^ 2 := by rw [norm_sq_one_dim, sq_abs]
  have h2 := congrArg Real.sqrt h
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (abs_nonneg _)] at h2

theorem continuous_eptSh (R : ℝ) : Continuous (eptSh R) :=
  (contDiff_ept_sub R).continuous

theorem measurePreserving_eptSh (R : ℝ) :
    MeasurePreserving (eptSh R) (volume : Measure ℝ)
      (volume : Measure (EuclideanSpace ℝ (Fin 1))) :=
  measurePreserving_ept.comp (measurePreserving_sub_right (volume : Measure ℝ) R)

/-- `eptSh R` as a measurable equivalence. -/
def eptShEquiv (R : ℝ) : ℝ ≃ᵐ EuclideanSpace ℝ (Fin 1) :=
  (MeasurableEquiv.subRight R).trans eptEquiv

theorem eptShEquiv_apply (R x : ℝ) : eptShEquiv R x = eptSh R x := rfl

theorem measurableEmbedding_eptSh (R : ℝ) : MeasurableEmbedding (eptSh R) :=
  (eptShEquiv R).measurableEmbedding

theorem eptSh_preimage_ball (R : ℝ) :
    eptSh R ⁻¹' (Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) R) = Set.Ioo 0 (2 * R) := by
  ext x
  have h : x ∈ eptSh R ⁻¹' (Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) R) ↔ |x - R| < R := by
    simp [eptSh, Metric.mem_ball, dist_eq_norm, ept_norm]
  rw [h, abs_lt, mem_Ioo]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-- **Reduction of ball integrals to interval integrals on `(0, 2R)`.** -/
theorem integral_ball_shift {R : ℝ} (hR : 0 ≤ R) (F : EuclideanSpace ℝ (Fin 1) → ℝ) :
    (∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) R, F z)
      = ∫ x in (0 : ℝ)..(2 * R), F (eptSh R x) := by
  rw [integral_ball_one hR F]
  have h1 : ∀ t : ℝ, F (ept t) = (fun y => F (eptSh R y)) (t + R) := by
    intro t
    simp [eptSh]
  simp only [h1]
  rw [intervalIntegral.integral_comp_add_right (fun y => F (eptSh R y)) R,
    show -R + R = (0 : ℝ) by ring, show R + R = 2 * R by ring]

theorem integrableOn_comp_eptSh {R : ℝ} (f : EuclideanSpace ℝ (Fin 1) → ℝ) :
    IntegrableOn (fun x => f (eptSh R x)) (Set.Ioo 0 (2 * R)) volume
      ↔ IntegrableOn f (Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) R) volume := by
  rw [← eptSh_preimage_ball R]
  exact (measurePreserving_eptSh R).integrableOn_comp_preimage (measurableEmbedding_eptSh R)

/-! ## Part 1. Test functions transplanted to the ball, and the weak derivative of a slice -/

/-- A test function `φ` on `(0, 2R)` lifted to the ball: `liftTest R φ z = φ (z₀ + R)`. -/
def liftTest (R : ℝ) (φ : ℝ → ℝ) : EuclideanSpace ℝ (Fin 1) → ℝ := fun z => φ (z 0 + R)

@[simp] theorem liftTest_apply (R : ℝ) (φ : ℝ → ℝ) (z : EuclideanSpace ℝ (Fin 1)) :
    liftTest R φ z = φ (z 0 + R) := rfl

theorem contDiff_coord (R : ℝ) : ContDiff ℝ ∞ (fun z : EuclideanSpace ℝ (Fin 1) => z 0 + R) := by
  have h0 : ContDiff ℝ ∞ (fun z : EuclideanSpace ℝ (Fin 1) => z 0) :=
    (EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).contDiff
  exact h0.add contDiff_const

theorem continuous_coord (R : ℝ) :
    Continuous (fun z : EuclideanSpace ℝ (Fin 1) => z 0 + R) := (contDiff_coord R).continuous

theorem contDiff_liftTest (R : ℝ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (liftTest R φ) := hφ.comp (contDiff_coord R)

theorem coord_preimage_eq_image (R : ℝ) (S : Set ℝ) :
    (fun z : EuclideanSpace ℝ (Fin 1) => z 0 + R) ⁻¹' S = eptSh R '' S := by
  ext z
  constructor
  · intro hz
    exact ⟨z 0 + R, hz, eptSh_coord R z⟩
  · rintro ⟨x, hx, rfl⟩
    simpa only [Set.mem_preimage, coord_eptSh] using hx

theorem coord_preimage_Ioo (R : ℝ) :
    (fun z : EuclideanSpace ℝ (Fin 1) => z 0 + R) ⁻¹' (Set.Ioo 0 (2 * R))
      = Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) R := by
  ext z
  simp only [Set.mem_preimage, Set.mem_Ioo, Metric.mem_ball, dist_eq_norm, sub_zero,
    norm_one_dim, abs_lt]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

theorem tsupport_liftTest_subset (R : ℝ) (φ : ℝ → ℝ) :
    tsupport (liftTest R φ)
      ⊆ (fun z : EuclideanSpace ℝ (Fin 1) => z 0 + R) ⁻¹' (tsupport φ) := by
  refine closure_minimal ?_ (IsClosed.preimage (continuous_coord R) isClosed_closure)
  intro z hz
  exact subset_closure (by simpa only [liftTest, Function.mem_support] using hz)

theorem hasCompactSupport_liftTest {R : ℝ} {φ : ℝ → ℝ} (hφc : HasCompactSupport φ) :
    HasCompactSupport (liftTest R φ) := by
  have hsub : tsupport (liftTest R φ) ⊆ eptSh R '' (tsupport φ) := by
    rw [← coord_preimage_eq_image]
    exact tsupport_liftTest_subset R φ
  exact IsCompact.of_isClosed_subset (hφc.isCompact.image (continuous_eptSh R))
    isClosed_closure hsub

theorem tsupport_liftTest_subset_ball {R : ℝ} {φ : ℝ → ℝ}
    (hφs : tsupport φ ⊆ Set.Ioo 0 (2 * R)) :
    tsupport (liftTest R φ) ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) R := by
  refine (tsupport_liftTest_subset R φ).trans ?_
  rw [← coord_preimage_Ioo R]
  exact Set.preimage_mono hφs

theorem fderiv_liftTest_single (R : ℝ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (z : EuclideanSpace ℝ (Fin 1)) :
    fderiv ℝ (liftTest R φ) z (EuclideanSpace.single (0 : Fin 1) 1) = deriv φ (z 0 + R) := by
  have hd : HasDerivAt φ (deriv φ (z 0 + R)) (z 0 + R) :=
    ((hφ.differentiable (by simp)) (z 0 + R)).hasDerivAt
  have h : HasFDerivAt (liftTest R φ)
      (deriv φ (z 0 + R) •
        (EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ)) z :=
    hd.comp_hasFDerivAt z (hasFDerivAt_coord R z)
  rw [h.fderiv]
  simp [EuclideanSpace.single_apply]

/-- **Deliverable 1.**  The slice `x ↦ v(ept (x − R))` of a weak-`H¹` function on the ball
has the coordinate `x ↦ (∇v)(ept (x − R))₀` of its weak gradient as a one-dimensional weak
derivative on `(0, 2R)`. -/
theorem hasWeakDeriv_slice {R : ℝ} (hR : 0 < R) (v : TransH1 1 R) :
    HasWeakDeriv 0 (2 * R) (fun x => v.toFun (eptSh R x)) (fun x => v.grad (eptSh R x) 0) := by
  intro φ hφ hφc hφs
  have h2R : (0 : ℝ) ≤ 2 * R := by linarith
  have hwg := v.hasWeakGrad (liftTest R φ) (contDiff_liftTest R hφ)
    (hasCompactSupport_liftTest hφc) (tsupport_liftTest_subset_ball hφs) 0
  have hL : (∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) R,
        v.toFun z * fderiv ℝ (liftTest R φ) z (EuclideanSpace.single (0 : Fin 1) 1))
      = ∫ x in Set.Ioo (0 : ℝ) (2 * R), v.toFun (eptSh R x) * deriv φ x := by
    simp only [fderiv_liftTest_single R hφ]
    rw [integral_ball_shift hR.le (fun z => v.toFun z * deriv φ (z 0 + R)),
      ← Sobolev.intervalIntegral_eq_setIntegral_Ioo h2R]
    simp
  have hR' : (∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) R,
        v.grad z 0 * liftTest R φ z)
      = ∫ x in Set.Ioo (0 : ℝ) (2 * R), v.grad (eptSh R x) 0 * φ x := by
    rw [integral_ball_shift hR.le (fun z => v.grad z 0 * liftTest R φ z),
      ← Sobolev.intervalIntegral_eq_setIntegral_Ioo h2R]
    simp
  rw [← hL, ← hR']
  exact hwg

/-! ## Part 2. The absolutely continuous representative on `[0, 2R]` -/

theorem isFiniteMeasure_ball (R : ℝ) :
    IsFiniteMeasure (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) R)) := by
  constructor
  rw [Measure.restrict_apply_univ]
  exact measure_ball_lt_top

theorem integrableOn_slice {R : ℝ} (v : TransH1 1 R) :
    IntegrableOn (fun x => v.toFun (eptSh R x)) (Set.Ioo 0 (2 * R)) volume := by
  haveI : IsFiniteMeasure (volume.restrict (ThinDomain.transverseBall 1 R)) :=
    isFiniteMeasure_ball R
  exact (integrableOn_comp_eptSh v.toFun).mpr (v.memL2.integrable one_le_two)

theorem memLp_grad_coord {R : ℝ} (v : TransH1 1 R) :
    MemLp (fun z : EuclideanSpace ℝ (Fin 1) => v.grad z 0) 2
      (volume.restrict (ThinDomain.transverseBall 1 R)) :=
  Weak.memLp_two_comp v.grad_memL2 0

theorem integrableOn_slice_grad {R : ℝ} (v : TransH1 1 R) :
    IntegrableOn (fun x => v.grad (eptSh R x) 0) (Set.Ioo 0 (2 * R)) volume := by
  haveI : IsFiniteMeasure (volume.restrict (ThinDomain.transverseBall 1 R)) :=
    isFiniteMeasure_ball R
  exact (integrableOn_comp_eptSh (fun z : EuclideanSpace ℝ (Fin 1) => v.grad z 0)).mpr
    ((memLp_grad_coord v).integrable one_le_two)

theorem integrableOn_slice_grad_sq {R : ℝ} (v : TransH1 1 R) :
    IntegrableOn (fun x => v.grad (eptSh R x) 0 ^ 2) (Set.Ioo 0 (2 * R)) volume := by
  have h := memLp_grad_coord v
  exact (integrableOn_comp_eptSh (fun z : EuclideanSpace ℝ (Fin 1) => v.grad z 0 ^ 2)).mpr
    ((memLp_two_iff_integrable_sq h.aestronglyMeasurable).1 h)

/-- **Deliverable 2.**  The absolutely continuous representative of `v ∈ H¹(B_1(R))` in the
concrete one-dimensional Sobolev layer `H¹(0, 2R)`, produced by the du Bois-Reymond bridge
`RobinCaps.Sobolev.exists_h1_of_hasWeakDeriv`. -/
def rep {R : ℝ} (hR : 0 < R) (v : TransH1 1 R) : Sobolev.H1 (2 * R) :=
  Classical.choose (Sobolev.exists_h1_of_hasWeakDeriv (by linarith : (0 : ℝ) < 2 * R)
    (integrableOn_slice v) (integrableOn_slice_grad v) (integrableOn_slice_grad_sq v)
    (hasWeakDeriv_slice hR v))

theorem rep_ae {R : ℝ} (hR : 0 < R) (v : TransH1 1 R) :
    (rep hR v).toFun =ᵐ[volume.restrict (Set.Ioo 0 (2 * R))] fun x => v.toFun (eptSh R x) :=
  (Classical.choose_spec (Sobolev.exists_h1_of_hasWeakDeriv (by linarith : (0 : ℝ) < 2 * R)
    (integrableOn_slice v) (integrableOn_slice_grad v) (integrableOn_slice_grad_sq v)
    (hasWeakDeriv_slice hR v))).1

theorem rep_deriv_ae {R : ℝ} (hR : 0 < R) (v : TransH1 1 R) :
    deriv (rep hR v).toFun =ᵐ[volume.restrict (Set.Ioo 0 (2 * R))]
      fun x => v.grad (eptSh R x) 0 :=
  (Classical.choose_spec (Sobolev.exists_h1_of_hasWeakDeriv (by linarith : (0 : ℝ) < 2 * R)
    (integrableOn_slice v) (integrableOn_slice_grad v) (integrableOn_slice_grad_sq v)
    (hasWeakDeriv_slice hR v))).2

/-- Two functions continuous on `[0,ℓ]` and a.e. equal on `(0,ℓ)` are equal on `[0,ℓ]`. -/
theorem eqOn_Icc_of_ae_eq_of_continuousOn {ℓ : ℝ} (hℓ : 0 < ℓ) {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 0 ℓ)) (hg : ContinuousOn g (Set.Icc 0 ℓ))
    (h : f =ᵐ[volume.restrict (Set.Ioo 0 ℓ)] g) : Set.EqOn f g (Set.Icc 0 ℓ) := by
  have hres : (volume : Measure ℝ).restrict (Set.Ioo 0 ℓ)
      = (volume : Measure ℝ).restrict (Set.Icc 0 ℓ) :=
    Measure.restrict_congr_set Ioo_ae_eq_Icc
  rw [hres] at h
  exact Measure.eqOn_Icc_of_ae_eq volume (ne_of_lt hℓ) h hf hg

/-- An element of the concrete model `H¹(0,ℓ)` is continuous on `[0,ℓ]`. -/
theorem H1_continuousOn {ℓ : ℝ} (hℓ : 0 < ℓ) (w : Sobolev.H1 ℓ) :
    ContinuousOn w.toFun (Set.Icc 0 ℓ) := by
  have h' := w.ac.continuousOn
  rwa [Set.uIcc_of_le hℓ.le] at h'

/-- Two elements of the concrete model `H¹(0,ℓ)` which agree a.e. on `(0,ℓ)` agree
everywhere on `[0,ℓ]`: both are continuous there. -/
theorem H1_eqOn_of_ae_eq {ℓ : ℝ} (hℓ : 0 < ℓ) (w₁ w₂ : Sobolev.H1 ℓ)
    (h : w₁.toFun =ᵐ[volume.restrict (Set.Ioo 0 ℓ)] w₂.toFun) :
    Set.EqOn w₁.toFun w₂.toFun (Set.Icc 0 ℓ) :=
  eqOn_Icc_of_ae_eq_of_continuousOn hℓ (H1_continuousOn hℓ w₁) (H1_continuousOn hℓ w₂) h

/-- **Uniqueness of the representative.**  Any `w : H¹(0,2R)` representing `v` agrees with
`rep hR v` on the *closed* interval `[0, 2R]`; in particular the endpoint values are
well defined functions of the a.e.-class of `v`. -/
theorem rep_unique {R : ℝ} (hR : 0 < R) (v : TransH1 1 R) (w : Sobolev.H1 (2 * R))
    (hw : w.toFun =ᵐ[volume.restrict (Set.Ioo 0 (2 * R))] fun x => v.toFun (eptSh R x)) :
    Set.EqOn w.toFun (rep hR v).toFun (Set.Icc 0 (2 * R)) :=
  H1_eqOn_of_ae_eq (by linarith) w (rep hR v) (hw.trans (rep_ae hR v).symm)

theorem rep_add {R : ℝ} (hR : 0 < R) (v w : TransH1 1 R) :
    Set.EqOn (rep hR (v + w)).toFun (rep hR v + rep hR w).toFun (Set.Icc 0 (2 * R)) := by
  refine H1_eqOn_of_ae_eq (by linarith) _ _ ?_
  filter_upwards [rep_ae hR (v + w), rep_ae hR v, rep_ae hR w] with x hx1 hx2 hx3
  rw [hx1, Sobolev.H1.add_toFun]
  show (v + w).toFun (eptSh R x) = (rep hR v).toFun x + (rep hR w).toFun x
  rw [hx2, hx3, Weak.H1.add_toFun]
  rfl

theorem rep_smul {R : ℝ} (hR : 0 < R) (c : ℝ) (v : TransH1 1 R) :
    Set.EqOn (rep hR (c • v)).toFun (c • rep hR v).toFun (Set.Icc 0 (2 * R)) := by
  refine H1_eqOn_of_ae_eq (by linarith) _ _ ?_
  filter_upwards [rep_ae hR (c • v), rep_ae hR v] with x hx1 hx2
  rw [hx1, Sobolev.H1.smul_toFun]
  show (c • v).toFun (eptSh R x) = c * (rep hR v).toFun x
  rw [hx2, Weak.H1.smul_toFun]
  rfl

/-! ## Part 3. The a.e.-invariant boundary (trace) form -/

/-- The trace of `v` at the left endpoint `−R` of the ball. -/
def trZero {R : ℝ} (hR : 0 < R) (v : TransH1 1 R) : ℝ := (rep hR v).toFun 0

/-- The trace of `v` at the right endpoint `R` of the ball. -/
def trEnd {R : ℝ} (hR : 0 < R) (v : TransH1 1 R) : ℝ := (rep hR v).toFun (2 * R)

theorem zero_mem_Icc {R : ℝ} (hR : 0 < R) : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (2 * R) :=
  ⟨le_rfl, by linarith⟩

theorem end_mem_Icc {R : ℝ} (hR : 0 < R) : (2 * R) ∈ Set.Icc (0 : ℝ) (2 * R) :=
  ⟨by linarith, le_rfl⟩

theorem trZero_add {R : ℝ} (hR : 0 < R) (v w : TransH1 1 R) :
    trZero hR (v + w) = trZero hR v + trZero hR w := by
  have h := rep_add hR v w (zero_mem_Icc hR)
  simpa only [trZero, Sobolev.H1.add_toFun, Pi.add_apply] using h

theorem trEnd_add {R : ℝ} (hR : 0 < R) (v w : TransH1 1 R) :
    trEnd hR (v + w) = trEnd hR v + trEnd hR w := by
  have h := rep_add hR v w (end_mem_Icc hR)
  simpa only [trEnd, Sobolev.H1.add_toFun, Pi.add_apply] using h

theorem trZero_smul {R : ℝ} (hR : 0 < R) (c : ℝ) (v : TransH1 1 R) :
    trZero hR (c • v) = c * trZero hR v := by
  have h := rep_smul hR c v (zero_mem_Icc hR)
  simpa only [trZero, Sobolev.H1.smul_toFun] using h

theorem trEnd_smul {R : ℝ} (hR : 0 < R) (c : ℝ) (v : TransH1 1 R) :
    trEnd hR (c • v) = c * trEnd hR v := by
  have h := rep_smul hR c v (end_mem_Icc hR)
  simpa only [trEnd, Sobolev.H1.smul_toFun] using h

/-- **The boundary (trace) form for `m = 1`, for `R > 0`.** -/
def bdTrPos {R : ℝ} (hR : 0 < R) : TransH1 1 R →ₗ[ℝ] TransH1 1 R →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v => trZero hR u * trZero hR v + trEnd hR u * trEnd hR v)
    (fun u v w => by simp only []; rw [trZero_add, trEnd_add]; ring)
    (fun c u v => by simp only [smul_eq_mul]; rw [trZero_smul, trEnd_smul]; ring)
    (fun u v w => by simp only []; rw [trZero_add, trEnd_add]; ring)
    (fun c u v => by simp only [smul_eq_mul]; rw [trZero_smul, trEnd_smul]; ring)

/-- **Deliverable 3.  The a.e.-invariant boundary form on `H¹(B_1(R))`** (the one-dimensional
trace), defined through the absolutely continuous representative of `RobinCaps.Sobolev.H1`. -/
def bdTr (R : ℝ) : TransH1 1 R →ₗ[ℝ] TransH1 1 R →ₗ[ℝ] ℝ :=
  if h : 0 < R then bdTrPos h else 0

theorem bdTr_of_pos {R : ℝ} (hR : 0 < R) : bdTr R = bdTrPos hR := dif_pos hR

@[simp] theorem bdTr_apply {R : ℝ} (hR : 0 < R) (u v : TransH1 1 R) :
    bdTr R u v = trZero hR u * trZero hR v + trEnd hR u * trEnd hR v := by
  rw [bdTr_of_pos hR]; rfl

theorem bdTr_symm (R : ℝ) (u v : TransH1 1 R) : bdTr R u v = bdTr R v u := by
  by_cases hR : 0 < R
  · rw [bdTr_apply hR, bdTr_apply hR]; ring
  · rw [bdTr, dif_neg hR]; simp

theorem bdTr_nonneg (R : ℝ) (v : TransH1 1 R) : 0 ≤ bdTr R v v := by
  by_cases hR : 0 < R
  · rw [bdTr_apply hR, ← pow_two, ← pow_two]; positivity
  · rw [bdTr, dif_neg hR]; simp

/-! ## Part 4. The three forms, read on the representative -/

theorem ae_uIoc_of_rep {R : ℝ} (hR : 0 < R) (v : TransH1 1 R) :
    ∀ᵐ x : ℝ, x ∈ Set.uIoc (0 : ℝ) (2 * R) → (rep hR v).toFun x = v.toFun (eptSh R x) := by
  rw [Set.uIoc_of_le (by linarith : (0 : ℝ) ≤ 2 * R), ← ae_restrict_iff' measurableSet_Ioc,
    ← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := 2 * R))]
  exact rep_ae hR v

theorem ae_uIoc_of_rep_deriv {R : ℝ} (hR : 0 < R) (v : TransH1 1 R) :
    ∀ᵐ x : ℝ, x ∈ Set.uIoc (0 : ℝ) (2 * R) →
      deriv (rep hR v).toFun x = v.grad (eptSh R x) 0 := by
  rw [Set.uIoc_of_le (by linarith : (0 : ℝ) ≤ 2 * R), ← ae_restrict_iff' measurableSet_Ioc,
    ← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := 2 * R))]
  exact rep_deriv_ae hR v

/-- **Deliverable 4a.**  The `L²(B_1(R))` inner product is the `L²(0,2R)` inner product of the
representatives. -/
theorem NBilin_eq_massBilin_rep {R : ℝ} (hR : 0 < R) (u v : TransH1 1 R) :
    NBilin u v = Sobolev.massBilin (2 * R) (rep hR u) (rep hR v) := by
  have h : NBilin u v
      = ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) R, u.toFun z * v.toFun z := rfl
  rw [h, integral_ball_shift hR.le (fun z => u.toFun z * v.toFun z)]
  refine (intervalIntegral.integral_congr_ae ?_).symm
  filter_upwards [ae_uIoc_of_rep hR u, ae_uIoc_of_rep hR v] with x hxu hxv hx
  rw [hxu hx, hxv hx]

/-- **Deliverable 4b.**  The Dirichlet bilinear form of the ball is the one-dimensional
Dirichlet form of the representatives. -/
theorem dirichletBilin_eq_rep {R : ℝ} (hR : 0 < R) (u v : TransH1 1 R) :
    dirichletBilin u v
      = ∫ x in (0 : ℝ)..(2 * R), deriv (rep hR u).toFun x * deriv (rep hR v).toFun x := by
  have h : dirichletBilin u v
      = ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) R, ⟪u.grad z, v.grad z⟫_ℝ := rfl
  rw [h]
  simp only [inner_one_dim]
  rw [integral_ball_shift hR.le (fun z => u.grad z 0 * v.grad z 0)]
  refine (intervalIntegral.integral_congr_ae ?_).symm
  filter_upwards [ae_uIoc_of_rep_deriv hR u, ae_uIoc_of_rep_deriv hR v] with x hxu hxv hx
  rw [hxu hx, hxv hx]

/-- **Deliverable 4c.**  The transverse Robin form with the trace boundary term is the
one-dimensional Robin form `a_{α,α;2R}` of the representatives. -/
theorem qBilin_eq_robinBilin_rep {R : ℝ} (hR : 0 < R) (α : ℝ) (u v : TransH1 1 R) :
    qBilin α (bdTr R) u v = Sobolev.robinBilin α α (2 * R) (rep hR u) (rep hR v) := by
  rw [qBilin_eq, dirichletBilin_eq_rep hR, bdTr_apply hR]
  unfold Sobolev.robinBilin
  simp only [trZero, trEnd]
  ring

theorem NB_eq_mass_rep {R : ℝ} (hR : 0 < R) (v : TransH1 1 R) :
    NB v = Sobolev.mass (2 * R) (rep hR v) := by
  rw [← NBilin_self v, NBilin_eq_massBilin_rep hR, Sobolev.massBilin_self]

theorem qB_eq_robinForm_rep {R : ℝ} (hR : 0 < R) (α : ℝ) (v : TransH1 1 R) :
    qB α (bdTr R) v = Sobolev.robinForm α α (2 * R) (rep hR v) := by
  rw [← qBilin_self α (bdTr R) v, qBilin_eq_robinBilin_rep hR, Sobolev.robinBilin_self]

/-! ### The trace form is a genuine trace -/

/-- For an element with a continuous representative, `rep` *is* the slice on all of
`[0, 2R]`. -/
theorem rep_eq_of_continuous {R : ℝ} (hR : 0 < R) (v : TransH1 1 R) (hv : Continuous v.toFun) :
    Set.EqOn (rep hR v).toFun (fun x => v.toFun (eptSh R x)) (Set.Icc 0 (2 * R)) :=
  eqOn_Icc_of_ae_eq_of_continuousOn (by linarith)
    (H1_continuousOn (by linarith) (rep hR v))
    (hv.comp (continuous_eptSh R)).continuousOn (rep_ae hR v)

theorem trZero_eq_of_continuous {R : ℝ} (hR : 0 < R) (v : TransH1 1 R)
    (hv : Continuous v.toFun) : trZero hR v = v.toFun (ept (-R)) := by
  have h := rep_eq_of_continuous hR v hv (zero_mem_Icc hR)
  rw [trZero, h]
  show v.toFun (ept (0 - R)) = _
  rw [show (0 : ℝ) - R = -R by ring]

theorem trEnd_eq_of_continuous {R : ℝ} (hR : 0 < R) (v : TransH1 1 R)
    (hv : Continuous v.toFun) : trEnd hR v = v.toFun (ept R) := by
  have h := rep_eq_of_continuous hR v hv (end_mem_Icc hR)
  rw [trEnd, h]
  show v.toFun (ept (2 * R - R)) = _
  rw [show 2 * R - R = R by ring]

/-- **Deliverable 3b.**  On elements with continuous representatives the trace form agrees with
the explicit endpoint form `bdPt` of `RobinCaps/Transverse/GroundStateOne.lean`. -/
theorem bdTr_eq_bdPt_of_continuous {R : ℝ} (hR : 0 < R) (u v : TransH1 1 R)
    (hu : Continuous u.toFun) (hv : Continuous v.toFun) : bdTr R u v = bdPt R u v := by
  rw [bdTr_apply hR, trZero_eq_of_continuous hR u hu, trZero_eq_of_continuous hR v hv,
    trEnd_eq_of_continuous hR u hu, trEnd_eq_of_continuous hR v hv, bdPt]
  ring

/-- **Deliverable 3c.**  The trace form is a.e.-invariant: it vanishes on elements whose
representative is a.e. zero on the ball. -/
theorem bdTr_vanishes {R : ℝ} (hR : 0 < R) (v w : TransH1 1 R)
    (hv : v.toFun =ᵐ[volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) R)]
      fun _ => (0 : ℝ)) : bdTr R v w = 0 := by
  have hmass : Sobolev.mass (2 * R) (rep hR v) = 0 := by
    rw [← NB_eq_mass_rep hR v]
    show Weak.mass v = 0
    unfold Weak.mass
    rw [integral_congr_ae (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · filter_upwards [hv] with z hz
      rw [hz]; ring
  have hnull : rep hR v ∈ Sobolev.nullOff (2 * R) :=
    Sobolev.mem_nullOff_of_mass_eq_zero (by linarith) hmass
  have huIcc : Set.uIcc (0 : ℝ) (2 * R) = Set.Icc (0 : ℝ) (2 * R) :=
    Set.uIcc_of_le (by linarith)
  have h0 : trZero hR v = 0 := hnull 0 (by rw [huIcc]; exact zero_mem_Icc hR)
  have h1 : trEnd hR v = 0 := hnull (2 * R) (by rw [huIcc]; exact end_mem_Icc hR)
  rw [bdTr_apply hR, h0, h1]
  ring

/-! ## Part 5. The weak eigenfunction identity against an arbitrary `H¹(0,ℓ)` element -/

/-- **Deliverable 5.**  The phase eigenfunction is a *weak* eigenfunction of the Robin form:
for **every** `W ∈ H¹(0,ℓ)`, `a_{p,q;ℓ}(e_j, W) = μ_j ⟪e_j, W⟫`.  The proof is the
one-dimensional integration by parts `RobinCaps.Transverse.ibp_lin`, which needs no
differentiability of `W`, together with the two Robin boundary conditions. -/
theorem robinBilin_phaseEigen_left (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ)
    {j : ℕ} (hj : 1 ≤ j) (W : Sobolev.H1 ℓ) :
    Sobolev.robinBilin p q ℓ (Sobolev.phaseEigenH1 p q ℓ j hp hq hℓ hj) W
      = Interval.mu p q ℓ j hp hq hℓ hj
        * Sobolev.massBilin ℓ (Sobolev.phaseEigenH1 p q ℓ j hp hq hℓ hj) W := by
  set k := Interval.phaseRoot p q ℓ j hp hq hℓ hj with hk
  set pe := Sobolev.phaseEigen p q ℓ j hp hq hℓ hj with hpe
  have hibp := ibp_lin W (le_refl (0 : ℝ)) hℓ.le (le_refl ℓ) (deriv pe)
    (fun x => -(k ^ 2) * pe x)
    (fun x _ => Sobolev.phaseEigen_deriv_hasDerivAt p q ℓ j hp hq hℓ hj x)
    ((continuous_const.mul (Sobolev.phaseEigen_continuous p q ℓ j hp hq hℓ hj)).continuousOn)
  have hswap : (∫ x in (0 : ℝ)..ℓ, deriv pe x * deriv W.toFun x)
      = ∫ x in (0 : ℝ)..ℓ, deriv W.toFun x * deriv pe x := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with x _
    ring
  have hI : (∫ x in (0 : ℝ)..ℓ, W.toFun x * (-(k ^ 2) * pe x))
      = -(k ^ 2) * ∫ x in (0 : ℝ)..ℓ, pe x * W.toFun x := by
    rw [show (fun x => W.toFun x * (-(k ^ 2) * pe x))
        = fun x => -(k ^ 2) * (pe x * W.toFun x) by funext x; ring,
      intervalIntegral.integral_const_mul]
  have hbz := Sobolev.phaseEigen_bc_zero p q ℓ j hp hq hℓ hj
  have hbl := Sobolev.phaseEigen_bc_ell p q ℓ j hp hq hℓ hj
  simp only [Sobolev.robinBilin, Sobolev.massBilin, Sobolev.phaseEigenH1_toFun, Interval.mu,
    ← hpe, ← hk]
  rw [hswap, hibp, hI, hbz, hbl]
  ring

/-! ## Part 6. The codimension-one lower bound `μ₂ ≤ Rayleigh` on the orthogonal complement -/

/-- **Deliverable 6.**  If `W ∈ H¹(0,ℓ)` is `L²`-orthogonal to the first phase eigenfunction,
then `μ₂ · N[W] ≤ a_{p,q;ℓ}[W]`.

The proof is the two-dimensional trial space `span {⟦e₁⟧, ⟦W⟧}` in the quotient `H1Q ℓ`.  The
weak eigenfunction identity `robinBilin_phaseEigen_left` makes this a *form-orthogonal* pair,
so the Rayleigh quotient on the span is at most `max (μ₁, a[W]/N[W])`; the min–max
characterisation `robinMinmaxQ_eq_mu` bounds `μ₂` by this maximum, and `μ₁ < μ₂` excludes the
first alternative. -/
theorem robinForm_ge_of_orth (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ)
    (h2 : (1 : ℕ) ≤ 2) (W : Sobolev.H1 ℓ)
    (horth : Sobolev.massBilin ℓ (Sobolev.phaseEigenH1 p q ℓ 1 hp hq hℓ (le_refl 1)) W = 0) :
    Interval.mu p q ℓ 2 hp hq hℓ h2 * Sobolev.mass ℓ W ≤ Sobolev.robinForm p q ℓ W := by
  classical
  set e₁ := Sobolev.phaseEigenH1 p q ℓ 1 hp hq hℓ (le_refl 1) with he₁
  set μ₁ := Interval.mu p q ℓ 1 hp hq hℓ (le_refl 1) with hμ₁
  have hm₁ : 0 < Sobolev.mass ℓ e₁ := Sobolev.phaseEigen_mass_pos p q ℓ (le_refl 1) hp hq hℓ
  rcases eq_or_lt_of_le (Sobolev.mass_nonneg ℓ W hℓ.le) with hmW | hmW
  · have hnull := Sobolev.mem_nullOff_of_mass_eq_zero hℓ hmW.symm
    have h0 : Sobolev.robinForm p q ℓ W = 0 := by
      rw [← Sobolev.robinBilin_self p q ℓ W]
      exact Sobolev.robinBilin_eq_zero_of_mem_nullOff p q hnull W
    rw [← hmW, h0, mul_zero]
  · set x : Sobolev.H1Q ℓ := Submodule.Quotient.mk e₁ with hx
    set y : Sobolev.H1Q ℓ := Submodule.Quotient.mk W with hy
    have hmx : Sobolev.massBilinQ ℓ x x = Sobolev.mass ℓ e₁ := by
      rw [hx, Sobolev.massBilinQ_mk, Sobolev.massBilin_self]
    have hmxy : Sobolev.massBilinQ ℓ x y = 0 := by
      rw [hx, hy, Sobolev.massBilinQ_mk]; exact horth
    have hmyx : Sobolev.massBilinQ ℓ y x = 0 := by
      rw [hx, hy, Sobolev.massBilinQ_mk, Sobolev.massBilin_comm]; exact horth
    have hmy : Sobolev.massBilinQ ℓ y y = Sobolev.mass ℓ W := by
      rw [hy, Sobolev.massBilinQ_mk, Sobolev.massBilin_self]
    have hrx : Sobolev.robinBilinQ p q ℓ x x = μ₁ * Sobolev.mass ℓ e₁ := by
      rw [hx, Sobolev.robinBilinQ_mk, Sobolev.robinBilin_self, hμ₁, he₁]
      exact Sobolev.phaseEigen_robinForm_eq p q ℓ (le_refl 1) hp hq hℓ
    have hrxy : Sobolev.robinBilinQ p q ℓ x y = 0 := by
      rw [hx, hy, Sobolev.robinBilinQ_mk, he₁,
        robinBilin_phaseEigen_left p q ℓ hp hq hℓ (le_refl 1) W, ← he₁, horth, mul_zero]
    have hryx : Sobolev.robinBilinQ p q ℓ y x = 0 := by
      rw [hx, hy, Sobolev.robinBilinQ_mk, Sobolev.robinBilin_comm, ← Sobolev.robinBilinQ_mk,
        ← hx, ← hy]
      exact hrxy
    have hry : Sobolev.robinBilinQ p q ℓ y y = Sobolev.robinForm p q ℓ W := by
      rw [hy, Sobolev.robinBilinQ_mk, Sobolev.robinBilin_self]
    -- linear independence of the pair in the quotient
    have hli : LinearIndependent ℝ ![x, y] := by
      rw [LinearIndependent.pair_iff]
      intro a b hab
      have hx' : Sobolev.massBilinQ ℓ x (a • x + b • y) = 0 := by rw [hab]; simp
      have hy' : Sobolev.massBilinQ ℓ y (a • x + b • y) = 0 := by rw [hab]; simp
      simp only [map_add, map_smul, smul_eq_mul, hmx, hmxy, hmy, hmyx, mul_zero, add_zero,
        zero_add] at hx' hy'
      constructor
      · have hxx : a * Sobolev.mass ℓ e₁ = 0 := by linarith
        rcases mul_eq_zero.1 hxx with h | h
        · exact h
        · exact absurd h (ne_of_gt hm₁)
      · have hyy : b * Sobolev.mass ℓ W = 0 := by linarith
        rcases mul_eq_zero.1 hyy with h | h
        · exact h
        · exact absurd h (ne_of_gt hmW)
    set t : ℝ := max μ₁ (Sobolev.robinForm p q ℓ W / Sobolev.mass ℓ W) with ht
    have hμ₁t : μ₁ ≤ t := le_max_left _ _
    have hQt : Sobolev.robinForm p q ℓ W ≤ t * Sobolev.mass ℓ W :=
      (div_le_iff₀ hmW).1 (le_max_right _ _)
    have hV : Module.finrank ℝ (Submodule.span ℝ (Set.range ![x, y])) = 2 := by
      rw [finrank_span_eq_card hli, Fintype.card_fin]
    have htrial : ∀ u ∈ Submodule.span ℝ (Set.range ![x, y]), u ≠ 0 →
        Sobolev.robinFormQ p q ℓ u ≤ t * Sobolev.massQ ℓ u := by
      intro u hu _
      rw [Submodule.mem_span_range_iff_exists_fun] at hu
      obtain ⟨c, rfl⟩ := hu
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
        Sobolev.robinFormQ, Sobolev.massQ, map_add, map_smul, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul, hmx, hmxy, hmyx, hmy, hrx, hrxy, hryx, hry]
      nlinarith [mul_le_mul_of_nonneg_left hμ₁t (mul_nonneg (mul_self_nonneg (c 0)) hm₁.le),
        mul_le_mul_of_nonneg_left hQt (mul_self_nonneg (c 1))]
    have hminmax : Sobolev.robinMinmaxQ p q ℓ 2 ≤ t :=
      Spectrum.minmax_le_of_trial' (Sobolev.robinFormQ p q ℓ) (Sobolev.massQ ℓ) 2 (by norm_num)
        (Sobolev.massQ_pos hℓ) (Sobolev.bddBelowRatio_robinFormQ p q ℓ hp.le hq.le hℓ.le)
        (Submodule.span ℝ (Set.range ![x, y])) hV t htrial
    rw [Sobolev.PiconeGeneral.robinMinmaxQ_eq_mu p q ℓ hp hq hℓ 2 h2] at hminmax
    have hlt : μ₁ < Interval.mu p q ℓ 2 hp hq hℓ h2 :=
      Sobolev.mu_lt_mu p q ℓ hp hq hℓ (le_refl 1) h2 (by norm_num)
    have hfin : Interval.mu p q ℓ 2 hp hq hℓ h2
        ≤ Sobolev.robinForm p q ℓ W / Sobolev.mass ℓ W := by
      rcases max_cases μ₁ (Sobolev.robinForm p q ℓ W / Sobolev.mass ℓ W) with
        ⟨hmax, _⟩ | ⟨hmax, _⟩
      · rw [ht, hmax] at hminmax; linarith
      · rw [ht, hmax] at hminmax; exact hminmax
    rw [le_div_iff₀ hmW] at hfin
    exact hfin

/-! ## Part 7. The transverse ground state for `m = 1` -/

theorem deriv_eq_of_eqOn_Icc {ℓ : ℝ} (u u' : ℝ → ℝ)
    (h : Set.EqOn u u' (Set.Icc 0 ℓ)) {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) ℓ) :
    deriv u x = deriv u' x := by
  have hev : u =ᶠ[nhds x] u' := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact h (Set.Ioo_subset_Icc_self hy)
  exact hev.deriv_eq

theorem robinBilin_congr_left {ℓ : ℝ} (hℓ : 0 < ℓ) (p q : ℝ) (u u' w : Sobolev.H1 ℓ)
    (h : Set.EqOn u.toFun u'.toFun (Set.Icc 0 ℓ)) :
    Sobolev.robinBilin p q ℓ u w = Sobolev.robinBilin p q ℓ u' w := by
  have h0 : u.toFun 0 = u'.toFun 0 := h ⟨le_rfl, hℓ.le⟩
  have hl : u.toFun ℓ = u'.toFun ℓ := h ⟨hℓ.le, le_rfl⟩
  have hint : (∫ x in (0 : ℝ)..ℓ, deriv u.toFun x * deriv w.toFun x)
      = ∫ x in (0 : ℝ)..ℓ, deriv u'.toFun x * deriv w.toFun x := by
    refine intervalIntegral.integral_congr_ae ?_
    have hae : ∀ᵐ x : ℝ, x ≠ ℓ := by rw [ae_iff]; simp
    filter_upwards [hae] with x hx hmem
    rw [Set.uIoc_of_le hℓ.le] at hmem
    rw [deriv_eq_of_eqOn_Icc u.toFun u'.toFun h ⟨hmem.1, lt_of_le_of_ne hmem.2 hx⟩]
  unfold Sobolev.robinBilin
  rw [hint, h0, hl]

theorem massBilin_congr_left {ℓ : ℝ} (hℓ : 0 < ℓ) (u u' w : Sobolev.H1 ℓ)
    (h : Set.EqOn u.toFun u'.toFun (Set.Icc 0 ℓ)) :
    Sobolev.massBilin ℓ u w = Sobolev.massBilin ℓ u' w := by
  unfold Sobolev.massBilin
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [Set.uIcc_of_le hℓ.le] at hx
  rw [h hx]

theorem mass_congr {ℓ : ℝ} (hℓ : 0 < ℓ) (u u' : Sobolev.H1 ℓ)
    (h : Set.EqOn u.toFun u'.toFun (Set.Icc 0 ℓ)) :
    Sobolev.mass ℓ u = Sobolev.mass ℓ u' := by
  unfold Sobolev.mass
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [Set.uIcc_of_le hℓ.le] at hx
  rw [h hx]

variable (α R : ℝ)

theorem slice_psi1 (hα : 0 < α) (hR : 0 < R) (x : ℝ) :
    (psi1 α R hα hR).toFun (eptSh R x) = gpFun α R hα hR x := by
  show gpFun α R hα hR ((eptSh R x) 0 + R) = _
  rw [coord_eptSh]

/-- The normalising constant of `psiN`. -/
def cN (α R : ℝ) (hα : 0 < α) (hR : 0 < R) : ℝ :=
  (Real.sqrt (Weak.mass (psi1 α R hα hR)))⁻¹

theorem cN_ne_zero (hα : 0 < α) (hR : 0 < R) : cN α R hα hR ≠ 0 :=
  inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (psi1_mass_pos α R hα hR)))

theorem psiN_eq_smul (hα : 0 < α) (hR : 0 < R) :
    psiN α R hα hR = cN α R hα hR • psi1 α R hα hR := rfl

/-- The representative of the normalised ground state is `c · e₁` on `[0, 2R]`. -/
theorem rep_psiN (hα : 0 < α) (hR : 0 < R) :
    Set.EqOn (cN α R hα hR • gpH1 α R hα hR).toFun
      (rep hR (psiN α R hα hR)).toFun (Set.Icc 0 (2 * R)) := by
  refine rep_unique hR (psiN α R hα hR) (cN α R hα hR • gpH1 α R hα hR) ?_
  filter_upwards with x
  show cN α R hα hR * gpFun α R hα hR x = (psiN α R hα hR).toFun (eptSh R x)
  rw [psiN_eq_smul]
  show _ = cN α R hα hR * (psi1 α R hα hR).toFun (eptSh R x)
  rw [slice_psi1]

theorem gpH1_eq_pe (hα : 0 < α) (hR : 0 < R) :
    gpH1 α R hα hR
      = Sobolev.phaseEigenH1 α α (2 * R) 1 hα hα (two_R_pos hR) (le_refl 1) := rfl

/-- **Deliverable 7a.  The weak eigenvalue equation for ALL `v ∈ H¹(B_1(R))`.** -/
theorem psiN_weak_eq (hα : 0 < α) (hR : 0 < R) (v : TransH1 1 R) :
    qBilin α (bdTr R) (psiN α R hα hR) v = nuR α R hα hR * NBilin (psiN α R hα hR) v := by
  have h2R : (0 : ℝ) < 2 * R := two_R_pos hR
  rw [qBilin_eq_robinBilin_rep hR, NBilin_eq_massBilin_rep hR,
    robinBilin_congr_left h2R α α _ (cN α R hα hR • gpH1 α R hα hR) _
      (rep_psiN α R hα hR).symm,
    massBilin_congr_left h2R _ (cN α R hα hR • gpH1 α R hα hR) _ (rep_psiN α R hα hR).symm,
    Sobolev.robinBilin_smul_left, Sobolev.massBilin_smul_left, gpH1_eq_pe,
    robinBilin_phaseEigen_left α α (2 * R) hα hα h2R (le_refl 1)]
  show _ = Interval.mu α α (2 * R) 1 hα hα h2R (le_refl 1) * _
  ring

/-- The gap constant of the `m = 1` transverse ground state. -/
def gapConstOne (α R : ℝ) (hα : 0 < α) (hR : 0 < R) : ℝ :=
  R ^ 2 * (lam2R α R hα hR - nuR α R hα hR)

theorem gapConstOne_pos (hα : 0 < α) (hR : 0 < R) : 0 < gapConstOne α R hα hR :=
  mul_pos (by positivity) (sub_pos.mpr (nuR_lt_lam2R α R hα hR))

/-- **Deliverable 7b.  The transverse gap in variational form.** -/
theorem psiN_gap (hα : 0 < α) (hR : 0 < R) (v : TransH1 1 R)
    (hv : NBilin (psiN α R hα hR) v = 0) :
    gapConstOne α R hα hR * R⁻¹ ^ 2 * NB v
      ≤ qB α (bdTr R) v - nuR α R hα hR * NB v := by
  have h2R : (0 : ℝ) < 2 * R := two_R_pos hR
  -- orthogonality of the representative to the first phase eigenfunction
  have horth : Sobolev.massBilin (2 * R)
      (Sobolev.phaseEigenH1 α α (2 * R) 1 hα hα h2R (le_refl 1)) (rep hR v) = 0 := by
    have h := hv
    rw [NBilin_eq_massBilin_rep hR,
      massBilin_congr_left h2R _ (cN α R hα hR • gpH1 α R hα hR) _
        (rep_psiN α R hα hR).symm, Sobolev.massBilin_smul_left, gpH1_eq_pe] at h
    rcases mul_eq_zero.1 h with h' | h'
    · exact absurd h' (cN_ne_zero α R hα hR)
    · exact h'
  have hkey := robinForm_ge_of_orth α α (2 * R) hα hα h2R (by norm_num) (rep hR v) horth
  have hmu2 : Interval.mu α α (2 * R) 2 hα hα h2R (by norm_num) = lam2R α R hα hR := rfl
  rw [hmu2] at hkey
  rw [← NB_eq_mass_rep hR, ← qB_eq_robinForm_rep hR α] at hkey
  have hRne : (R : ℝ) ≠ 0 := ne_of_gt hR
  have hfac : gapConstOne α R hα hR * R⁻¹ ^ 2 = lam2R α R hα hR - nuR α R hα hR := by
    unfold gapConstOne
    field_simp
  rw [hfac]
  linarith

/-- **Deliverable 7.  The transverse Robin ground state of `B_1(R)`, in full.** -/
def groundStateOne (α R : ℝ) (hα : 0 < α) (hR : 0 < R) :
    ThinDomain.TransverseGroundState 1 α R (bdTr R) where
  bdSymm := bdTr_symm R
  bdNonneg := bdTr_nonneg R
  psi := psiN α R hα hR
  nu := nuR α R hα hR
  normalized := psiN_normalized α R hα hR
  weak_eq := psiN_weak_eq α R hα hR
  gapConst := gapConstOne α R hα hR
  gapConst_pos := gapConstOne_pos α R hα hR
  gap := psiN_gap α R hα hR

theorem hasTransverseGroundStateOne (α R : ℝ) (hα : 0 < α) (hR : 0 < R) :
    ThinDomain.HasTransverseGroundState 1 α R (bdTr R) :=
  ⟨groundStateOne α R hα hR⟩

/-- **The quantitative transverse gap.**  For small `R` the gap constant of
`groundStateOne` is bounded below by a positive constant independent of `R`. -/
theorem groundStateOne_gap_quant (α : ℝ) (hα : 0 < α) :
    ∃ c R₀ : ℝ, 0 < c ∧ 0 < R₀ ∧ ∀ R : ℝ, ∀ hR : 0 < R, R < R₀ →
      c ≤ (groundStateOne α R hα hR).gapConst := by
  obtain ⟨c, R₀, hc, hR₀, hgap⟩ := transverse_gap_oneDim α hα
  refine ⟨c, R₀, hc, hR₀, ?_⟩
  intro R hR hRlt
  have h := hgap R hR hRlt
  show c ≤ gapConstOne α R hα hR
  unfold gapConstOne
  have hRne : (R : ℝ) ≠ 0 := ne_of_gt hR
  have hsq : (0 : ℝ) < R ^ 2 := by positivity
  have hinv : c * R⁻¹ ^ 2 * R ^ 2 = c := by field_simp
  nlinarith [mul_le_mul_of_nonneg_right h hsq.le]

/-! ### The three targets of `RobinCaps/Transverse/GroundStateOne.lean`, discharged -/

theorem traceOneTarget (R : ℝ) (hR : 0 < R) : TraceOneTarget R :=
  ⟨bdTr R, bdTr_symm R, bdTr_nonneg R,
    fun u v hu hv => bdTr_eq_bdPt_of_continuous hR u v hu hv⟩

theorem groundStateOneTarget (α R : ℝ) (hα : 0 < α) (hR : 0 < R) :
    GroundStateOneTarget α R :=
  ⟨bdTr R, ⟨groundStateOne α R hα hR⟩,
    fun u v hu hv => bdTr_eq_bdPt_of_continuous hR u v hu hv⟩

theorem gapFieldOneTarget (α R : ℝ) (hα : 0 < α) (hR : 0 < R) :
    GapFieldOneTarget α R hα hR (bdTr R) :=
  ⟨gapConstOne α R hα hR, gapConstOne_pos α R hα hR, psiN_gap α R hα hR⟩

end RobinCaps.Transverse

end

