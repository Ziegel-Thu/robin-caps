import RobinCaps.ThinDomain.H1P
import RobinCaps.Sobolev.DuBoisReymond

/-!
# Slice-wise (ACL) properties of the product weak-`H¹` space

This file proves the two "absolutely continuous on lines" (ACL) statements for the product
weak Sobolev layer `RobinCaps.ThinDomain.H1P` on a **cylinder**

`Ω = (a,b) ×ˢ B ⊆ CapSpace m = ℝ × EuclideanSpace ℝ (Fin m)`, `B` open,

which are the two targets `SliceACLAxial` and `SliceACL` recorded in
`RobinCaps/ThinDomain/H1P.lean`.

## Contents

* `prodTestS φ χ`: the product test function `(x,z) ↦ φ x * χ z`, its smoothness, its compact
  support and its two partial derivatives (`fderiv_prodTestS_axial`,
  `fderiv_prodTest_transverse`).
* `sliceAxial_of_test`, `sliceTransverse_of_test` (**deliverable 1**): for a *fixed* test
  function, Fubini plus the fundamental lemma of the calculus of variations in the transverse
  (resp. axial) variable give the one-dimensional integration-by-parts identity on almost
  every slice.  The exceptional null set still depends on the test function.
* `stepBumpFun`, `idxBump`: a countable family of smooth bumps (rational endpoints, integer
  sharpness) converging pointwise to indicators of rational intervals, and the one-dimensional
  upgrade `hasWeakDeriv_of_idxBump`: testing against this *countable* family is enough to
  characterise the weak derivative.  Ingredients: `setIntegral_eq_zero_of_stepBump` (dominated
  convergence) and `ae_eq_zero_of_setIntegral_Ioo_rat` (a function whose integral over every
  rational subinterval vanishes is `0` a.e.).
* `sliceACL_axial` (**deliverable 2**): for almost every `z`, `x ↦ u(x,z)` has `x ↦ ∂ₓu(x,z)`
  as a weak derivative on all of `(a,b)`; `sliceACLAxial_prod` is the `SliceACLAxial` target
  and `sliceACL_axial_h1` produces the absolutely continuous representative in
  `RobinCaps.Sobolev.H1 ℓ` on each line of the cylinder `(0,ℓ) × B`.
* `sliceACL_transverse` (**deliverable 3**): for almost every `x`, `z ↦ u(x,z)` has
  `z ↦ ∇_z u(x,z)` as a weak gradient on `B`, in the sense of
  `RobinCaps.Sobolev.Weak.HasWeakGrad`; `sliceACL_prod` is the `SliceACL` target.  Here the
  test function is removed from the null set by separability of `L²(B)` instead (see the
  discussion before `SliceACLTransverse`).

Everything is proved without `sorry`, `axiom` or `admit`.
-/
open MeasureTheory Set Filter

open scoped ContDiff ENNReal Topology

namespace RobinCaps.ThinDomain

noncomputable section

variable {m : ℕ}

/-! ### Product test functions -/

/-- The product test function `Φ(x,z) = φ(x) · χ(z)` on `CapSpace m`. -/
def prodTestS (φ : ℝ → ℝ) (χ : EuclideanSpace ℝ (Fin m) → ℝ) : CapSpace m → ℝ :=
  fun p => φ p.1 * χ p.2

variable {φ : ℝ → ℝ} {χ : EuclideanSpace ℝ (Fin m) → ℝ}

@[simp] theorem prodTestS_apply (p : CapSpace m) : prodTestS φ χ p = φ p.1 * χ p.2 := rfl

theorem prodTest_contDiff (hφ : ContDiff ℝ ∞ φ) (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (prodTestS φ χ) :=
  (hφ.comp contDiff_fst).mul (hχ.comp contDiff_snd)

theorem prodTest_tsupport : tsupport (prodTestS φ χ) ⊆ tsupport φ ×ˢ tsupport χ := by
  have hs : Function.support (prodTestS φ χ) ⊆ Function.support φ ×ˢ Function.support χ := by
    intro p hp
    have hne : φ p.1 * χ p.2 ≠ 0 := hp
    exact ⟨fun h => hne (by rw [h, zero_mul]), fun h => hne (by rw [h, mul_zero])⟩
  refine (closure_mono hs).trans ?_
  rw [closure_prod_eq]
  exact subset_rfl

theorem prodTest_hasCompactSupport (hφc : HasCompactSupport φ) (hχc : HasCompactSupport χ) :
    HasCompactSupport (prodTestS φ χ) :=
  IsCompact.of_isClosed_subset (IsCompact.prod hφc hχc) isClosed_closure prodTest_tsupport

/-- The derivative of a product test function, as a `HasFDerivAt` statement. -/
theorem hasFDerivAt_prodTest (hφ : ContDiff ℝ ∞ φ) (hχ : ContDiff ℝ ∞ χ) (p : CapSpace m) :
    HasFDerivAt (prodTestS φ χ)
      (φ p.1 • (fderiv ℝ χ p.2).comp
          (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin m)))
        + χ p.2 • (fderiv ℝ φ p.1).comp
          (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin m)))) p := by
  have hf : HasFDerivAt (fun q : CapSpace m => φ q.1)
      ((fderiv ℝ φ p.1).comp (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin m)))) p :=
    HasFDerivAt.comp p ((hφ.differentiable (by simp)).differentiableAt.hasFDerivAt)
      (hasFDerivAt_fst)
  have hg : HasFDerivAt (fun q : CapSpace m => χ q.2)
      ((fderiv ℝ χ p.2).comp (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin m)))) p :=
    HasFDerivAt.comp p ((hχ.differentiable (by simp)).differentiableAt.hasFDerivAt)
      (hasFDerivAt_snd)
  exact hf.mul hg

/-- The **axial** partial derivative of a product test function. -/
theorem fderiv_prodTestS_axial (hφ : ContDiff ℝ ∞ φ) (hχ : ContDiff ℝ ∞ χ) (p : CapSpace m) :
    fderiv ℝ (prodTestS φ χ) p (1, 0) = deriv φ p.1 * χ p.2 := by
  rw [(hasFDerivAt_prodTest hφ hχ p).fderiv]
  simp [mul_comm]

/-- The **transverse** partial derivatives of a product test function. -/
theorem fderiv_prodTest_transverse (hφ : ContDiff ℝ ∞ φ) (hχ : ContDiff ℝ ∞ χ) (p : CapSpace m)
    (i : Fin m) :
    fderiv ℝ (prodTestS φ χ) p (0, EuclideanSpace.single i 1)
      = φ p.1 * fderiv ℝ χ p.2 (EuclideanSpace.single i 1) := by
  rw [(hasFDerivAt_prodTest hφ hχ p).fderiv]
  simp

/-! ### The product domain `Ω = (a,b) × B` -/

variable {a b : ℝ} {B : Set (EuclideanSpace ℝ (Fin m))}

/-- The volume of `CapSpace m` restricted to a product set is the product of the restrictions. -/
theorem restrict_prodDomain (a b : ℝ) (B : Set (EuclideanSpace ℝ (Fin m))) :
    (volume : Measure (CapSpace m)).restrict (Ioo a b ×ˢ B)
      = ((volume : Measure ℝ).restrict (Ioo a b)).prod
          ((volume : Measure (EuclideanSpace ℝ (Fin m))).restrict B) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]

/-- A bounded-in-`z` product slab has finite volume. -/
theorem volume_prod_ne_top {S : Set (EuclideanSpace ℝ (Fin m))} (hS : volume S ≠ (⊤ : ℝ≥0∞)) :
    (volume : Measure (CapSpace m)) (Ioo a b ×ˢ S) ≠ (⊤ : ℝ≥0∞) := by
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  exact ENNReal.mul_ne_top (by simp [Real.volume_Ioo]) hS

/-- An `L²(Ω)` function times a bounded continuous function is integrable on any subset of `Ω`
of finite measure. -/
theorem integrable_mul_of_memLp_two_of_finite {Ω Ω' : Set (CapSpace m)} {u v : CapSpace m → ℝ}
    (hu : MemLp u 2 (volume.restrict Ω)) (hsub : Ω' ⊆ Ω)
    (hfin : (volume : Measure (CapSpace m)) Ω' ≠ (⊤ : ℝ≥0∞))
    (hv : Continuous v) {C : ℝ} (hC : ∀ p, ‖v p‖ ≤ C) :
    Integrable (fun p => u p * v p) (volume.restrict Ω') := by
  have hres : (volume.restrict Ω).restrict Ω' = (volume : Measure (CapSpace m)).restrict Ω' :=
    Measure.restrict_restrict_of_subset hsub
  have hu' : MemLp u 2 ((volume : Measure (CapSpace m)).restrict Ω') := by
    rw [← hres]; exact hu.restrict Ω'
  haveI : IsFiniteMeasure ((volume : Measure (CapSpace m)).restrict Ω') :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hfin⟩
  exact (hu'.integrable one_le_two).mul_bdd hv.aestronglyMeasurable (.of_forall hC)

/-! ### Axial slices: the identity for a fixed test function -/

/-- The `z`-slice pairing `z ↦ ∫_a^b (u(x,z) φ'(x) + ∂ₓu(x,z) φ(x)) dx` is locally integrable
on `B`. -/
theorem locallyIntegrableOn_axialPairing (hB : IsOpen B) (u : H1P (Ioo a b ×ˢ B))
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    LocallyIntegrableOn
      (fun z => ∫ x in Ioo a b, (u.toFun (x, z) * deriv φ x + u.gx (x, z) * φ x)) B
      (volume.restrict B) := by
  have hφ' : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.1 hφ).2
  obtain ⟨C₁, hC₁⟩ := hφc.deriv.exists_bound_of_continuous hφ'.continuous
  obtain ⟨C₂, hC₂⟩ := hφc.exists_bound_of_continuous hφ.continuous
  intro z₀ hz₀
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hB z₀ hz₀
  refine ⟨Metric.ball z₀ r, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z₀ hr), ?_⟩
  have hres : (volume.restrict B).restrict (Metric.ball z₀ r)
      = (volume : Measure (EuclideanSpace ℝ (Fin m))).restrict (Metric.ball z₀ r) :=
    Measure.restrict_restrict_of_subset hball
  rw [IntegrableOn, hres]
  have hsub : Ioo a b ×ˢ Metric.ball z₀ r ⊆ Ioo a b ×ˢ B := Set.prod_mono subset_rfl hball
  have hfin : (volume : Measure (CapSpace m)) (Ioo a b ×ˢ Metric.ball z₀ r) ≠ (⊤ : ℝ≥0∞) :=
    volume_prod_ne_top measure_ball_lt_top.ne
  have h1 : Integrable (fun p : CapSpace m => u.toFun p * deriv φ p.1)
      (volume.restrict (Ioo a b ×ˢ Metric.ball z₀ r)) :=
    integrable_mul_of_memLp_two_of_finite u.memL2 hsub hfin
      (hφ'.continuous.comp continuous_fst) (fun p => hC₁ p.1)
  have h2 : Integrable (fun p : CapSpace m => u.gx p * φ p.1)
      (volume.restrict (Ioo a b ×ˢ Metric.ball z₀ r)) :=
    integrable_mul_of_memLp_two_of_finite u.gx_memL2 hsub hfin
      (hφ.continuous.comp continuous_fst) (fun p => hC₂ p.1)
  have h12 := h1.add h2
  rw [restrict_prodDomain] at h12
  exact h12.integral_prod_right

/-- **Fubini for product test functions (axial direction).**  For a fixed axial test function
`φ`, the slice pairing is orthogonal to every transverse test function `χ`. -/
theorem integral_axialPairing_mul_test (u : H1P (Ioo a b ×ˢ B))
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo a b)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ B) :
    ∫ z in B, χ z * (∫ x in Ioo a b, (u.toFun (x, z) * deriv φ x + u.gx (x, z) * φ x)) = 0 := by
  have hΦ : ContDiff ℝ ∞ (prodTestS φ χ) := prodTest_contDiff hφ hχ
  have hΦc : HasCompactSupport (prodTestS φ χ) := prodTest_hasCompactSupport hφc hχc
  have hΦs : tsupport (prodTestS φ χ) ⊆ Ioo a b ×ˢ B :=
    prodTest_tsupport.trans (Set.prod_mono hφs hχs)
  obtain ⟨key, -⟩ := u.hasWeakGrad (prodTestS φ χ) hΦ hΦc hΦs
  have hF1 : Integrable (fun p => u.toFun p * fderiv ℝ (prodTestS φ χ) p (1, 0))
      (volume.restrict (Ioo a b ×ˢ B)) := integrable_mul_dirDeriv u.memL2 hΦ hΦc _
  have hF2 : Integrable (fun p => u.gx p * prodTestS φ χ p)
      (volume.restrict (Ioo a b ×ˢ B)) := integrable_gx_mul u.gx_memL2 hΦ hΦc
  have hzero : ∫ p in Ioo a b ×ˢ B,
      (u.toFun p * fderiv ℝ (prodTestS φ χ) p (1, 0) + u.gx p * prodTestS φ χ p) = 0 := by
    rw [integral_add hF1 hF2, key]; ring
  have hFsum : Integrable (fun p : CapSpace m =>
      u.toFun p * fderiv ℝ (prodTestS φ χ) p (1, 0) + u.gx p * prodTestS φ χ p)
      (volume.restrict (Ioo a b ×ˢ B)) := hF1.add hF2
  rw [restrict_prodDomain] at hzero hFsum
  rw [integral_prod_symm _ hFsum] at hzero
  rw [← hzero]
  refine integral_congr_ae (.of_forall fun z => ?_)
  have hpt : ∀ x : ℝ,
      u.toFun (x, z) * fderiv ℝ (prodTestS φ χ) (x, z) (1, 0)
          + u.gx (x, z) * prodTestS φ χ (x, z)
        = (u.toFun (x, z) * deriv φ x + u.gx (x, z) * φ x) * χ z := by
    intro x
    rw [fderiv_prodTestS_axial hφ hχ (x, z), prodTestS_apply]
    ring
  calc χ z * (∫ x in Ioo a b, (u.toFun (x, z) * deriv φ x + u.gx (x, z) * φ x))
      = (∫ x in Ioo a b, (u.toFun (x, z) * deriv φ x + u.gx (x, z) * φ x)) * χ z := mul_comm _ _
    _ = ∫ x in Ioo a b, (u.toFun (x, z) * deriv φ x + u.gx (x, z) * φ x) * χ z :=
        (integral_mul_const _ _).symm
    _ = ∫ x in Ioo a b, (u.toFun (x, z) * fderiv ℝ (prodTestS φ χ) (x, z) (1, 0)
          + u.gx (x, z) * prodTestS φ χ (x, z)) :=
        integral_congr_ae (.of_forall fun x => (hpt x).symm)

/-- **Deliverable 1 (axial).**  For every fixed axial test function `φ`, almost every
transverse slice satisfies the one-dimensional integration-by-parts identity. -/
theorem sliceAxial_of_test (hB : IsOpen B) (u : H1P (Ioo a b ×ˢ B))
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo a b) :
    ∀ᵐ z ∂(volume.restrict B),
      (∫ x in Ioo a b, (u.toFun (x, z) * deriv φ x + u.gx (x, z) * φ x)) = 0 := by
  have hvan : ∀ᵐ z ∂(volume.restrict B), z ∈ B →
      (∫ x in Ioo a b, (u.toFun (x, z) * deriv φ x + u.gx (x, z) * φ x)) = 0 := by
    refine hB.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (locallyIntegrableOn_axialPairing hB u hφ hφc) ?_
    intro χ hχ hχc hχs
    simpa [smul_eq_mul] using integral_axialPairing_mul_test u hφ hφc hφs hχ hχc hχs
  filter_upwards [hvan, ae_restrict_mem hB.measurableSet] with z hz hzB using hz hzB

/-! ### Transverse slices: the identity for a fixed test function -/

/-- An `L²(Ω)` function times a bounded continuous function that vanishes off a set `S` meeting
`Ω` in finite measure is integrable on `Ω`. -/
theorem integrable_mul_of_memLp_two_of_support {Ω S : Set (CapSpace m)} {u v : CapSpace m → ℝ}
    (hu : MemLp u 2 (volume.restrict Ω)) (hS : MeasurableSet S)
    (hfin : (volume : Measure (CapSpace m)) (S ∩ Ω) ≠ (⊤ : ℝ≥0∞))
    (hv : Continuous v) {C : ℝ} (hC : ∀ p, ‖v p‖ ≤ C) (hvan : ∀ p ∉ S, v p = 0) :
    Integrable (fun p => u p * v p) (volume.restrict Ω) := by
  have hind : (fun p => u p * v p) = S.indicator (fun p => u p * v p) := by
    funext p
    by_cases hp : p ∈ S
    · rw [Set.indicator_of_mem hp]
    · rw [Set.indicator_of_notMem hp, hvan p hp, mul_zero]
  rw [hind, integrable_indicator_iff hS, IntegrableOn, Measure.restrict_restrict hS]
  exact integrable_mul_of_memLp_two_of_finite hu inter_subset_right hfin hv hC

/-- The slab `ℝ × tsupport χ` meets the cylinder in a set of finite measure. -/
theorem volume_slab_inter_ne_top (hχc : HasCompactSupport χ) :
    (volume : Measure (CapSpace m))
      (((univ : Set ℝ) ×ˢ tsupport χ) ∩ (Ioo a b ×ˢ B)) ≠ (⊤ : ℝ≥0∞) := by
  rw [Set.prod_inter_prod, univ_inter]
  refine volume_prod_ne_top (ne_of_lt (lt_of_le_of_lt (measure_mono inter_subset_left) ?_))
  exact hχc.measure_lt_top

/-- The `x`-slice pairing `x ↦ ∫_B (u(x,z) ∂ᵢχ(z) + (∇_z u)ᵢ(x,z) χ(z)) dz` is locally
integrable on `(a,b)`. -/
theorem locallyIntegrableOn_transversePairing (u : H1P (Ioo a b ×ˢ B))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (i : Fin m) :
    LocallyIntegrableOn
      (fun x => ∫ z in B, (u.toFun (x, z) * fderiv ℝ χ z (EuclideanSpace.single i 1)
        + u.gz (x, z) i * χ z)) (Ioo a b) (volume.restrict (Ioo a b)) := by
  have hcont : Continuous fun z : EuclideanSpace ℝ (Fin m) =>
      fderiv ℝ χ z (EuclideanSpace.single i 1) :=
    (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨C₁, hC₁⟩ := (hχc.fderiv_apply ℝ (EuclideanSpace.single i 1)).exists_bound_of_continuous
    hcont
  obtain ⟨C₂, hC₂⟩ := hχc.exists_bound_of_continuous hχ.continuous
  have hSmeas : MeasurableSet ((univ : Set ℝ) ×ˢ tsupport χ) :=
    MeasurableSet.prod MeasurableSet.univ (isClosed_tsupport χ).measurableSet
  have hvan₁ : ∀ p : CapSpace m, p ∉ (univ : Set ℝ) ×ˢ tsupport χ →
      fderiv ℝ χ p.2 (EuclideanSpace.single i 1) = 0 := by
    intro p hp
    have hp2 : p.2 ∉ tsupport χ := fun h => hp ⟨mem_univ _, h⟩
    rw [fderiv_of_notMem_tsupport ℝ hp2]; rfl
  have hvan₂ : ∀ p : CapSpace m, p ∉ (univ : Set ℝ) ×ˢ tsupport χ → χ p.2 = 0 := by
    intro p hp
    exact image_eq_zero_of_notMem_tsupport fun h => hp ⟨mem_univ _, h⟩
  have h1 : Integrable (fun p : CapSpace m =>
      u.toFun p * fderiv ℝ χ p.2 (EuclideanSpace.single i 1))
      (volume.restrict (Ioo a b ×ˢ B)) :=
    integrable_mul_of_memLp_two_of_support u.memL2 hSmeas (volume_slab_inter_ne_top hχc)
      (hcont.comp continuous_snd) (fun p => hC₁ p.2) hvan₁
  have h2 : Integrable (fun p : CapSpace m => u.gz p i * χ p.2)
      (volume.restrict (Ioo a b ×ˢ B)) :=
    integrable_mul_of_memLp_two_of_support (memLp_two_compP u.gz_memL2 i) hSmeas
      (volume_slab_inter_ne_top hχc) (hχ.continuous.comp continuous_snd) (fun p => hC₂ p.2) hvan₂
  have h12 : Integrable (fun p : CapSpace m =>
      u.toFun p * fderiv ℝ χ p.2 (EuclideanSpace.single i 1) + u.gz p i * χ p.2)
      (volume.restrict (Ioo a b ×ˢ B)) := h1.add h2
  rw [restrict_prodDomain] at h12
  intro x hx
  refine ⟨Ioo a b, self_mem_nhdsWithin, ?_⟩
  rw [IntegrableOn, Measure.restrict_restrict_of_subset subset_rfl]
  exact h12.integral_prod_left

/-- **Fubini for product test functions (transverse direction).** -/
theorem integral_transversePairing_mul_test (u : H1P (Ioo a b ×ˢ B))
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo a b)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ B) (i : Fin m) :
    ∫ x in Ioo a b, φ x * (∫ z in B, (u.toFun (x, z) * fderiv ℝ χ z (EuclideanSpace.single i 1)
      + u.gz (x, z) i * χ z)) = 0 := by
  have hΦ : ContDiff ℝ ∞ (prodTestS φ χ) := prodTest_contDiff hφ hχ
  have hΦc : HasCompactSupport (prodTestS φ χ) := prodTest_hasCompactSupport hφc hχc
  have hΦs : tsupport (prodTestS φ χ) ⊆ Ioo a b ×ˢ B :=
    prodTest_tsupport.trans (Set.prod_mono hφs hχs)
  obtain ⟨-, key⟩ := u.hasWeakGrad (prodTestS φ χ) hΦ hΦc hΦs
  have hF1 : Integrable (fun p =>
      u.toFun p * fderiv ℝ (prodTestS φ χ) p (0, EuclideanSpace.single i 1))
      (volume.restrict (Ioo a b ×ˢ B)) := integrable_mul_dirDeriv u.memL2 hΦ hΦc _
  have hF2 : Integrable (fun p => u.gz p i * prodTestS φ χ p)
      (volume.restrict (Ioo a b ×ˢ B)) := integrable_compP_mul u.gz_memL2 hΦ hΦc i
  have hzero : ∫ p in Ioo a b ×ˢ B,
      (u.toFun p * fderiv ℝ (prodTestS φ χ) p (0, EuclideanSpace.single i 1)
        + u.gz p i * prodTestS φ χ p) = 0 := by
    rw [integral_add hF1 hF2, key i]; ring
  have hFsum : Integrable (fun p : CapSpace m =>
      u.toFun p * fderiv ℝ (prodTestS φ χ) p (0, EuclideanSpace.single i 1)
        + u.gz p i * prodTestS φ χ p) (volume.restrict (Ioo a b ×ˢ B)) := hF1.add hF2
  rw [restrict_prodDomain] at hzero hFsum
  rw [integral_prod _ hFsum] at hzero
  rw [← hzero]
  refine integral_congr_ae (.of_forall fun x => ?_)
  have hpt : ∀ z : EuclideanSpace ℝ (Fin m),
      u.toFun (x, z) * fderiv ℝ (prodTestS φ χ) (x, z) (0, EuclideanSpace.single i 1)
          + u.gz (x, z) i * prodTestS φ χ (x, z)
        = φ x * (u.toFun (x, z) * fderiv ℝ χ z (EuclideanSpace.single i 1)
            + u.gz (x, z) i * χ z) := by
    intro z
    rw [fderiv_prodTest_transverse hφ hχ (x, z) i, prodTestS_apply]
    ring
  calc φ x * (∫ z in B, (u.toFun (x, z) * fderiv ℝ χ z (EuclideanSpace.single i 1)
          + u.gz (x, z) i * χ z))
      = ∫ z in B, φ x * (u.toFun (x, z) * fderiv ℝ χ z (EuclideanSpace.single i 1)
          + u.gz (x, z) i * χ z) := (integral_const_mul _ _).symm
    _ = ∫ z in B, (u.toFun (x, z) * fderiv ℝ (prodTestS φ χ) (x, z) (0, EuclideanSpace.single i 1)
          + u.gz (x, z) i * prodTestS φ χ (x, z)) :=
        integral_congr_ae (.of_forall fun z => (hpt z).symm)

/-- **Deliverable 1 (transverse).**  For every fixed transverse test function `χ` and every
coordinate `i`, almost every axial slice satisfies the integration-by-parts identity. -/
theorem sliceTransverse_of_test (u : H1P (Ioo a b ×ˢ B))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ B) (i : Fin m) :
    ∀ᵐ x ∂(volume.restrict (Ioo a b)),
      (∫ z in B, (u.toFun (x, z) * fderiv ℝ χ z (EuclideanSpace.single i 1)
        + u.gz (x, z) i * χ z)) = 0 := by
  have hvan : ∀ᵐ x ∂(volume.restrict (Ioo a b)), x ∈ Ioo a b →
      (∫ z in B, (u.toFun (x, z) * fderiv ℝ χ z (EuclideanSpace.single i 1)
        + u.gz (x, z) i * χ z)) = 0 := by
    refine isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (locallyIntegrableOn_transversePairing u hχ hχc i) ?_
    intro φ hφ hφc hφs
    simpa [smul_eq_mul] using
      integral_transversePairing_mul_test u hφ hφc hφs hχ hχc hχs i
  filter_upwards [hvan, ae_restrict_mem measurableSet_Ioo] with x hx hxI using hx hxI

/-! ### A countable family of smooth bumps on `ℝ`

The upgrade from "for each test function, almost every slice" to "almost every slice, for all
test functions" needs a *countable* family of test functions.  We use the smooth bumps
`stepBumpFun c r n`, which are `1` on `[c - r(n+1)/(n+2), c + r(n+1)/(n+2)]` and supported in
`[c - r, c + r]`; as `n → ∞` they converge pointwise to the indicator of `(c-r, c+r)`.  Taking
`c, r` with rational endpoints gives a countable family. -/

/-- The bump data: equal to `1` on `closedBall c (r (n+1)/(n+2))`, supported in
`closedBall c r`. -/
def stepBumpData (c r : ℝ) (hr : 0 < r) (n : ℕ) : ContDiffBump c where
  rIn := r * (((n : ℝ) + 1) / ((n : ℝ) + 2))
  rIn_pos := mul_pos hr (by positivity)
  rOut := r
  rIn_lt_rOut := by
    refine mul_lt_of_lt_one_right hr ?_
    rw [div_lt_one (by positivity)]
    linarith

/-- The `n`-th smooth approximation of the indicator of `(c - r, c + r)` (junk for `r ≤ 0`). -/
def stepBumpFun (c r : ℝ) (n : ℕ) : ℝ → ℝ :=
  if h : 0 < r then fun x => stepBumpData c r h n x else fun _ => 0

theorem stepBumpFun_of_pos {r : ℝ} (c : ℝ) (hr : 0 < r) (n : ℕ) :
    stepBumpFun c r n = fun x => stepBumpData c r hr n x := dif_pos hr

theorem stepBumpFun_contDiff {r : ℝ} (c : ℝ) (hr : 0 < r) (n : ℕ) :
    ContDiff ℝ ∞ (stepBumpFun c r n) := by
  rw [stepBumpFun_of_pos c hr n]
  exact (stepBumpData c r hr n).contDiff

theorem stepBumpFun_tsupport {r : ℝ} (c : ℝ) (hr : 0 < r) (n : ℕ) :
    tsupport (stepBumpFun c r n) = Icc (c - r) (c + r) := by
  rw [stepBumpFun_of_pos c hr n]
  have : (fun x => stepBumpData c r hr n x) = ⇑(stepBumpData c r hr n) := rfl
  rw [this, ContDiffBump.tsupport_eq, Real.closedBall_eq_Icc]
  rfl

theorem stepBumpFun_hasCompactSupport {r : ℝ} (c : ℝ) (hr : 0 < r) (n : ℕ) :
    HasCompactSupport (stepBumpFun c r n) := by
  rw [HasCompactSupport, stepBumpFun_tsupport c hr n]
  exact isCompact_Icc

theorem stepBumpFun_nonneg (c r : ℝ) (n : ℕ) (x : ℝ) : 0 ≤ stepBumpFun c r n x := by
  rw [stepBumpFun]
  split
  · exact ContDiffBump.nonneg _
  · exact le_rfl

theorem stepBumpFun_le_one (c r : ℝ) (n : ℕ) (x : ℝ) : stepBumpFun c r n x ≤ 1 := by
  rw [stepBumpFun]
  split
  · exact ContDiffBump.le_one _
  · exact zero_le_one

theorem stepBumpFun_eq_zero {c r : ℝ} (hr : 0 < r) (n : ℕ) {x : ℝ}
    (hx : x ∉ Ioo (c - r) (c + r)) : stepBumpFun c r n x = 0 := by
  rw [stepBumpFun_of_pos c hr n]
  refine ContDiffBump.zero_of_le_dist _ ?_
  simp only [mem_Ioo, not_and_or, not_lt] at hx
  have hd : r ≤ |x - c| := by
    rcases hx with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  simpa [Real.dist_eq] using hd

theorem stepBumpFun_eventually_one {c r : ℝ} (hr : 0 < r) {x : ℝ}
    (hx : x ∈ Ioo (c - r) (c + r)) : ∀ᶠ n : ℕ in atTop, stepBumpFun c r n x = 1 := by
  obtain ⟨hx1, hx2⟩ := hx
  have hd : |x - c| < r := by
    rw [abs_lt]; constructor <;> linarith
  set ε : ℝ := r - |x - c| with hεdef
  have hε : 0 < ε := by simp only [hεdef]; linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (r / ε)
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [stepBumpFun_of_pos c hr n]
  refine ContDiffBump.one_of_mem_closedBall _ ?_
  have hNn : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hn
  have hpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have h1 : r / ε < (n : ℝ) + 2 := by linarith
  have h2 : r / ((n : ℝ) + 2) < ε := by
    rw [div_lt_iff₀ hpos]
    rw [div_lt_iff₀ hε] at h1
    linarith
  have h3 : r * (((n : ℝ) + 1) / ((n : ℝ) + 2)) = r - r / ((n : ℝ) + 2) := by
    field_simp
    ring
  have : |x - c| ≤ r * (((n : ℝ) + 1) / ((n : ℝ) + 2)) := by
    rw [h3]
    simp only [hεdef] at h2
    linarith
  simpa [Real.dist_eq] using this

/-! ### From the bump family to vanishing on rational intervals, and to `0` a.e. -/

/-- If the pairing of `W` with all the bumps `stepBumpFun c r n`, `n : ℕ`, vanishes, then the
integral of `W` over `(c-r, c+r)` vanishes.  (Dominated convergence.) -/
theorem setIntegral_eq_zero_of_stepBump {a b c r : ℝ} {W : ℝ → ℝ} (hr : 0 < r)
    (hW : IntegrableOn W (Ioo a b)) (hsub : Ioo (c - r) (c + r) ⊆ Ioo a b)
    (h : ∀ n : ℕ, ∫ x in Ioo a b, W x * stepBumpFun c r n x = 0) :
    ∫ x in Ioo (c - r) (c + r), W x = 0 := by
  have hlim : Tendsto (fun n : ℕ => ∫ x in Ioo a b, W x * stepBumpFun c r n x) atTop
      (𝓝 (∫ x in Ioo a b, W x * (Ioo (c - r) (c + r)).indicator (fun _ => (1 : ℝ)) x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => |W x|) (fun n => ?_) hW.abs
      (fun n => ?_) ?_
    · exact hW.aestronglyMeasurable.mul
        (stepBumpFun_contDiff c hr n).continuous.aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (stepBumpFun_nonneg c r n x)]
      exact mul_le_of_le_one_right (abs_nonneg _) (stepBumpFun_le_one c r n x)
    · filter_upwards with x
      by_cases hx : x ∈ Ioo (c - r) (c + r)
      · rw [Set.indicator_of_mem hx]
        refine Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [stepBumpFun_eventually_one hr hx] with n hn
        rw [hn]
      · rw [Set.indicator_of_notMem hx]
        refine Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards with n
        rw [stepBumpFun_eq_zero hr n hx]
  simp only [h] at hlim
  have hzero := tendsto_nhds_unique tendsto_const_nhds hlim
  have hrw : (∫ x in Ioo a b, W x * (Ioo (c - r) (c + r)).indicator (fun _ => (1 : ℝ)) x)
      = ∫ x in Ioo (c - r) (c + r), W x := by
    have h1 : (∫ x in Ioo a b, W x * (Ioo (c - r) (c + r)).indicator (fun _ => (1 : ℝ)) x)
        = ∫ x in Ioo a b, (Ioo (c - r) (c + r)).indicator W x := by
      refine integral_congr_ae (.of_forall fun x => ?_)
      by_cases hx : x ∈ Ioo (c - r) (c + r) <;> simp [hx]
    rw [h1, setIntegral_indicator measurableSet_Ioo, inter_eq_right.2 hsub]
  rw [hrw] at hzero
  exact hzero.symm

/-- **A function whose integral over every rational subinterval vanishes is zero a.e.** -/
theorem ae_eq_zero_of_setIntegral_Ioo_rat {a b : ℝ} {W : ℝ → ℝ} (hab : a < b)
    (hW : IntegrableOn W (Ioo a b))
    (h : ∀ s t : ℚ, a < (s : ℝ) → ((s : ℝ) < (t : ℝ)) → ((t : ℝ) < b) →
      ∫ x in Ioo (s : ℝ) (t : ℝ), W x = 0) :
    W =ᵐ[volume.restrict (Ioo a b)] 0 := by
  have hWI : IntervalIntegrable W volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 hW
  have hmid : ((a + b) / 2) ∈ Icc a b := ⟨by linarith, by linarith⟩
  set V : ℝ → ℝ := fun y => ∫ x in ((a + b) / 2)..y, W x with hVdef
  have hVcont : ContinuousOn V (uIcc a b) :=
    intervalIntegral.continuousOn_primitive_interval' hWI
      (by rw [uIcc_of_le hab.le]; exact hmid)
  have hVIoo : ContinuousOn V (Ioo a b) :=
    hVcont.mono (by rw [uIcc_of_le hab.le]; exact Ioo_subset_Icc_self)
  have hII : ∀ y ∈ Icc a b, IntervalIntegrable W volume ((a + b) / 2) y := by
    intro y hy
    refine hWI.mono_set ?_
    rw [uIcc_of_le hab.le]
    exact uIcc_subset_Icc hmid hy
  -- `V` takes the same value at all rational points of `(a,b)`.
  have hVrat : ∀ s t : ℚ, a < (s : ℝ) → ((s : ℝ) < b) → a < (t : ℝ) → ((t : ℝ) < b) →
      V s = V t := by
    have hlt : ∀ s t : ℚ, a < (s : ℝ) → ((s : ℝ) < (t : ℝ)) → ((t : ℝ) < b) → V s = V t := by
      intro s t hs hst htb
      have hsb : (s : ℝ) < b := lt_trans hst htb
      have hat : a < (t : ℝ) := lt_trans hs hst
      have hsub := intervalIntegral.integral_interval_sub_left
        (hII (t : ℝ) ⟨hat.le, htb.le⟩) (hII (s : ℝ) ⟨hs.le, hsb.le⟩)
      have hIoo : (∫ x in (s : ℝ)..(t : ℝ), W x) = ∫ x in Ioo (s : ℝ) (t : ℝ), W x :=
        RobinCaps.Sobolev.intervalIntegral_eq_setIntegral_Ioo hst.le
      rw [hIoo, h s t hs hst htb] at hsub
      simp only [hVdef]
      linarith
    intro s t hs hsb ht htb
    rcases lt_trichotomy (s : ℝ) (t : ℝ) with hst | hst | hst
    · exact hlt s t hs hst htb
    · rw [hst]
    · exact (hlt t s ht hst hsb).symm
  obtain ⟨q₀, hq₀a, hq₀b⟩ := exists_rat_btwn hab
  have hEq : EqOn V (fun _ => V (q₀ : ℝ)) (Ioo a b ∩ Set.range ((↑) : ℚ → ℝ)) := by
    rintro x ⟨hxI, q, rfl⟩
    exact hVrat q q₀ hxI.1 hxI.2 hq₀a hq₀b
  have hconst : EqOn V (fun _ => V (q₀ : ℝ)) (Ioo a b) :=
    hEq.of_subset_closure hVIoo continuousOn_const inter_subset_left
      (Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo)
  -- hence `W` pairs to zero against every test function.
  refine RobinCaps.Sobolev.ae_eq_zero_of_integral_mul_test_eq_zero hW ?_
  intro φ hφ hφc hφs
  have hVW : RobinCaps.Sobolev.HasWeakDeriv a b V W :=
    RobinCaps.Sobolev.hasWeakDeriv_primitive hab hW hmid
  have hkey := hVW φ hφ hφc hφs
  have hφ' : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.1 hφ).2
  have hdsupp : tsupport (deriv φ) ⊆ Ioo a b :=
    (closure_minimal support_deriv_subset isClosed_closure).trans hφs
  have hderiv : (∫ x in Ioo a b, deriv φ x) = 0 := by
    rw [RobinCaps.Sobolev.setIntegral_test_eq_integral hdsupp]
    exact integral_deriv_eq_zero_of_compactSupport
      (fun x => (hφ.differentiable (by simp) x).hasDerivAt) hφ'.continuous hφc
  have hVint : (∫ x in Ioo a b, V x * deriv φ x) = 0 := by
    have : (∫ x in Ioo a b, V x * deriv φ x) = ∫ x in Ioo a b, V (q₀ : ℝ) * deriv φ x := by
      refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
      rw [hconst hx]
    rw [this, integral_const_mul, hderiv, mul_zero]
  rw [hVint] at hkey
  linarith [hkey]

/-! ### The countable family of test functions and the one-dimensional upgrade -/

instance isFiniteMeasure_restrict_Ioo_slice (a b : ℝ) :
    IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioo a b)) :=
  ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioo]; exact ENNReal.ofReal_lt_top⟩

/-- The primitive of an integrable function is integrable on the interval. -/
theorem integrableOn_primitive {a b : ℝ} (hab : a < b) {g : ℝ → ℝ}
    (hg : IntegrableOn g (Ioo a b)) :
    IntegrableOn (fun x => ∫ t in ((a + b) / 2)..x, g t) (Ioo a b) := by
  have hgI : IntervalIntegrable g volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 hg
  have hcont : ContinuousOn (fun x => ∫ t in ((a + b) / 2)..x, g t) (uIcc a b) :=
    intervalIntegral.continuousOn_primitive_interval' hgI
      (by rw [uIcc_of_le hab.le]; exact ⟨by linarith, by linarith⟩)
  rw [uIcc_of_le hab.le] at hcont
  exact (hcont.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self

/-- The integral of the derivative of a test function over `(a,b)` vanishes. -/
theorem setIntegral_deriv_test_eq_zero {a b : ℝ} {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo a b) :
    ∫ x in Ioo a b, deriv φ x = 0 := by
  have hφ' : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.1 hφ).2
  have hdsupp : tsupport (deriv φ) ⊆ Ioo a b :=
    (closure_minimal support_deriv_subset isClosed_closure).trans hφs
  rw [RobinCaps.Sobolev.setIntegral_test_eq_integral hdsupp]
  exact integral_deriv_eq_zero_of_compactSupport
    (fun x => (hφ.differentiable (by simp) x).hasDerivAt) hφ'.continuous hφc

/-- Adding a constant does not change the weak derivative. -/
theorem hasWeakDeriv_const_add {a b : ℝ} {v g : ℝ → ℝ} (hv : IntegrableOn v (Ioo a b))
    (h : RobinCaps.Sobolev.HasWeakDeriv a b v g) (c : ℝ) :
    RobinCaps.Sobolev.HasWeakDeriv a b (fun x => c + v x) g := by
  intro φ hφ hφc hφs
  have hφ' : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.1 hφ).2
  have h1 : IntegrableOn (fun x => v x * deriv φ x) (Ioo a b) :=
    RobinCaps.Sobolev.integrableOn_mul_test hv hφ'.continuous hφc.deriv
  have h2 : IntegrableOn (fun x => c * deriv φ x) (Ioo a b) := by
    refine Integrable.const_mul ?_ c
    exact (hφ'.continuous.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hsplit : (∫ x in Ioo a b, (c + v x) * deriv φ x)
      = (∫ x in Ioo a b, c * deriv φ x) + ∫ x in Ioo a b, v x * deriv φ x := by
    rw [← integral_add h2 h1]
    exact integral_congr_ae (.of_forall fun x => by ring)
  rw [hsplit, integral_const_mul, setIntegral_deriv_test_eq_zero hφ hφc hφs, mul_zero, zero_add]
  exact h φ hφ hφc hφs

/-- The weak derivative only depends on the a.e. class of the function. -/
theorem hasWeakDeriv_congr_ae {a b : ℝ} {v v' g : ℝ → ℝ}
    (hvv : v =ᵐ[volume.restrict (Ioo a b)] v') (h : RobinCaps.Sobolev.HasWeakDeriv a b v g) :
    RobinCaps.Sobolev.HasWeakDeriv a b v' g := by
  intro φ hφ hφc hφs
  rw [← h φ hφ hφc hφs]
  exact integral_congr_ae (hvv.mono fun x hx => by simp only [hx])

/-- The countable family of bumps: `k = (s, t, n)` gives the `n`-th smooth approximation of the
indicator of the interval with rational endpoints `(s, t)`. -/
def idxBump (k : ℚ × ℚ × ℕ) : ℝ → ℝ :=
  stepBumpFun (((k.1 : ℝ) + (k.2.1 : ℝ)) / 2) (((k.2.1 : ℝ) - (k.1 : ℝ)) / 2) k.2.2

theorem idxBump_contDiff {k : ℚ × ℚ × ℕ} (hk : (k.1 : ℝ) < (k.2.1 : ℝ)) :
    ContDiff ℝ ∞ (idxBump k) := stepBumpFun_contDiff _ (by linarith) _

theorem idxBump_hasCompactSupport {k : ℚ × ℚ × ℕ} (hk : (k.1 : ℝ) < (k.2.1 : ℝ)) :
    HasCompactSupport (idxBump k) := stepBumpFun_hasCompactSupport _ (by linarith) _

theorem idxBump_tsupport {k : ℚ × ℚ × ℕ} (hk : (k.1 : ℝ) < (k.2.1 : ℝ)) :
    tsupport (idxBump k) = Icc (k.1 : ℝ) (k.2.1 : ℝ) := by
  rw [idxBump, stepBumpFun_tsupport _ (by linarith : (0:ℝ) < ((k.2.1 : ℝ) - (k.1 : ℝ)) / 2)]
  congr 1 <;> ring

/-- **du Bois-Reymond from countably many test functions.**  If `v` and `g` are integrable on
`(a,b)` and the (equivalent, integrated) identity holds for the countable family `idxBump`,
then `g` is a weak derivative of `v` on `(a,b)`. -/
theorem hasWeakDeriv_of_idxBump {a b : ℝ} (hab : a < b) {v g : ℝ → ℝ}
    (hv : IntegrableOn v (Ioo a b)) (hg : IntegrableOn g (Ioo a b))
    (h : ∀ k : ℚ × ℚ × ℕ, a < (k.1 : ℝ) → ((k.1 : ℝ) < (k.2.1 : ℝ)) → ((k.2.1 : ℝ) < b) →
      ∫ x in Ioo a b, (v x - ∫ t in ((a + b) / 2)..x, g t) *
        (idxBump k x - (∫ y, idxBump k y) * RobinCaps.Sobolev.bump hab x) = 0) :
    RobinCaps.Sobolev.HasWeakDeriv a b v g := by
  have hρsmooth : ContDiff ℝ ∞ (RobinCaps.Sobolev.bump hab) :=
    RobinCaps.Sobolev.bump_contDiff hab
  have hρc : HasCompactSupport (RobinCaps.Sobolev.bump hab) :=
    RobinCaps.Sobolev.bump_hasCompactSupport hab
  have hPvint : IntegrableOn (fun x => ∫ t in ((a + b) / 2)..x, g t) (Ioo a b) :=
    integrableOn_primitive hab hg
  have hwint : IntegrableOn (fun x => v x - ∫ t in ((a + b) / 2)..x, g t) (Ioo a b) :=
    hv.sub hPvint
  set cc : ℝ := ∫ x in Ioo a b, (v x - ∫ t in ((a + b) / 2)..x, g t) *
      RobinCaps.Sobolev.bump hab x with hccdef
  have hWint : IntegrableOn (fun x => (v x - ∫ t in ((a + b) / 2)..x, g t) - cc) (Ioo a b) :=
    hwint.sub (integrable_const cc)
  -- Step 1: the pairing of `W` with each bump of the family vanishes.
  have step1 : ∀ k : ℚ × ℚ × ℕ, a < (k.1 : ℝ) → ((k.1 : ℝ) < (k.2.1 : ℝ)) → ((k.2.1 : ℝ) < b) →
      ∫ x in Ioo a b, ((v x - ∫ t in ((a + b) / 2)..x, g t) - cc) * idxBump k x = 0 := by
    intro k h1 h2 h3
    have hφ : ContDiff ℝ ∞ (idxBump k) := idxBump_contDiff h2
    have hφc : HasCompactSupport (idxBump k) := idxBump_hasCompactSupport h2
    have hφs : tsupport (idxBump k) ⊆ Ioo a b := by
      rw [idxBump_tsupport h2]; exact Icc_subset_Ioo h1 h3
    have hI : ∫ x in Ioo a b, idxBump k x = ∫ y, idxBump k y :=
      RobinCaps.Sobolev.setIntegral_test_eq_integral hφs
    have e1 : IntegrableOn (fun x => (v x - ∫ t in ((a + b) / 2)..x, g t) * idxBump k x)
        (Ioo a b) := RobinCaps.Sobolev.integrableOn_mul_test hwint hφ.continuous hφc
    have e2 : IntegrableOn (fun x => (v x - ∫ t in ((a + b) / 2)..x, g t) *
        ((∫ y, idxBump k y) * RobinCaps.Sobolev.bump hab x)) (Ioo a b) :=
      RobinCaps.Sobolev.integrableOn_mul_test hwint
        (continuous_const.mul hρsmooth.continuous) hρc.mul_left
    have e3 : IntegrableOn (fun x => cc * idxBump k x) (Ioo a b) :=
      Integrable.const_mul ((hφ.continuous.integrableOn_Icc).mono_set Ioo_subset_Icc_self) cc
    have hIcc : ∫ x in Ioo a b, (v x - ∫ t in ((a + b) / 2)..x, g t) *
        ((∫ y, idxBump k y) * RobinCaps.Sobolev.bump hab x) = (∫ y, idxBump k y) * cc := by
      rw [hccdef, ← integral_const_mul]
      exact integral_congr_ae (.of_forall fun x => by ring)
    have hexp : ∫ x in Ioo a b, (v x - ∫ t in ((a + b) / 2)..x, g t) *
        (idxBump k x - (∫ y, idxBump k y) * RobinCaps.Sobolev.bump hab x)
        = (∫ x in Ioo a b, (v x - ∫ t in ((a + b) / 2)..x, g t) * idxBump k x)
          - (∫ y, idxBump k y) * cc := by
      rw [← hIcc, ← integral_sub e1 e2]
      exact integral_congr_ae (.of_forall fun x => by ring)
    have hkey := h k h1 h2 h3
    rw [hexp] at hkey
    have hfinal : ∫ x in Ioo a b, ((v x - ∫ t in ((a + b) / 2)..x, g t) - cc) * idxBump k x
        = (∫ x in Ioo a b, (v x - ∫ t in ((a + b) / 2)..x, g t) * idxBump k x)
          - cc * ∫ x in Ioo a b, idxBump k x := by
      rw [← integral_const_mul, ← integral_sub e1 e3]
      exact integral_congr_ae (.of_forall fun x => by ring)
    rw [hfinal, hI]
    linarith
  -- Step 2: the integral of `W` over every rational subinterval vanishes.
  have step2 : ∀ s t : ℚ, a < (s : ℝ) → ((s : ℝ) < (t : ℝ)) → ((t : ℝ) < b) →
      ∫ x in Ioo (s : ℝ) (t : ℝ), ((v x - ∫ y in ((a + b) / 2)..x, g y) - cc) = 0 := by
    intro s t h1 h2 h3
    have hr : (0 : ℝ) < ((t : ℝ) - (s : ℝ)) / 2 := by linarith
    have hc1 : ((s : ℝ) + (t : ℝ)) / 2 - ((t : ℝ) - (s : ℝ)) / 2 = (s : ℝ) := by ring
    have hc2 : ((s : ℝ) + (t : ℝ)) / 2 + ((t : ℝ) - (s : ℝ)) / 2 = (t : ℝ) := by ring
    have hsub : Ioo (((s : ℝ) + (t : ℝ)) / 2 - ((t : ℝ) - (s : ℝ)) / 2)
        (((s : ℝ) + (t : ℝ)) / 2 + ((t : ℝ) - (s : ℝ)) / 2) ⊆ Ioo a b := by
      rw [hc1, hc2]; exact Ioo_subset_Ioo h1.le h3.le
    have := setIntegral_eq_zero_of_stepBump hr hWint hsub
      (fun n => step1 (s, t, n) h1 h2 h3)
    rwa [hc1, hc2] at this
  -- Step 3: hence `W = 0` a.e., i.e. `v` is a constant plus the primitive of `g`.
  have hWzero : (fun x => (v x - ∫ t in ((a + b) / 2)..x, g t) - cc)
      =ᵐ[volume.restrict (Ioo a b)] 0 :=
    ae_eq_zero_of_setIntegral_Ioo_rat hab hWint step2
  have hvae : (fun x => cc + ∫ t in ((a + b) / 2)..x, g t)
      =ᵐ[volume.restrict (Ioo a b)] v := by
    filter_upwards [hWzero] with x hx
    have hx' : (v x - ∫ t in ((a + b) / 2)..x, g t) - cc = 0 := hx
    linarith
  exact hasWeakDeriv_congr_ae hvae
    (hasWeakDeriv_const_add hPvint
      (RobinCaps.Sobolev.hasWeakDeriv_primitive hab hg ⟨by linarith, by linarith⟩) cc)

/-! ### Deliverable 2: almost every axial slice has a weak derivative -/

theorem tsupport_sub_const_mul_subset {X : Type*} [TopologicalSpace X] (f g : X → ℝ) (c : ℝ) :
    tsupport (fun x => f x - c * g x) ⊆ tsupport f ∪ tsupport g := by
  have hsub : Function.support (fun x => f x - c * g x)
      ⊆ Function.support f ∪ Function.support g := by
    intro x hx
    by_contra hc
    rw [Set.mem_union, not_or] at hc
    have h1 : f x = 0 := by simpa using hc.1
    have h2 : g x = 0 := by simpa using hc.2
    exact hx (by simp [h1, h2])
  exact (closure_mono hsub).trans closure_union.subset

/-- Almost every axial slice of an `L²(Ω)` function is integrable (and square integrable) on
the axial interval. -/
theorem ae_integrableOn_axialSlice {f : CapSpace m → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo a b ×ˢ B))) :
    ∀ᵐ z ∂(volume.restrict B), IntegrableOn (fun x => f (x, z)) (Ioo a b) ∧
      IntegrableOn (fun x => f (x, z) ^ 2) (Ioo a b) := by
  have hsq : Integrable (fun p => f p ^ 2) (volume.restrict (Ioo a b ×ˢ B)) := hf.integrable_sq
  have hmeas : AEStronglyMeasurable f (volume.restrict (Ioo a b ×ˢ B)) := hf.aestronglyMeasurable
  rw [restrict_prodDomain] at hsq hmeas
  filter_upwards [hsq.prod_left_ae, hmeas.prodMk_right] with z h1 h2
  exact ⟨((memLp_two_iff_integrable_sq h2).2 h1).integrable one_le_two, h1⟩

/-- **Deliverable 2 (ACL in the axial direction).**  For almost every transverse coordinate
`z`, the axial slice `x ↦ u(x,z)` has the slice `x ↦ (∂ₓu)(x,z)` as a weak derivative on the
whole interval `(a,b)`. -/
theorem sliceACL_axial (hab : a < b) (hB : IsOpen B) (u : H1P (Ioo a b ×ˢ B)) :
    ∀ᵐ z ∂(volume.restrict B),
      RobinCaps.Sobolev.HasWeakDeriv a b (fun x => u.toFun (x, z)) (fun x => u.gx (x, z)) := by
  have hmid : ((a + b) / 2) ∈ Icc a b := ⟨by linarith, by linarith⟩
  have hu := ae_integrableOn_axialSlice (a := a) (b := b) (B := B) u.memL2
  have hgx := ae_integrableOn_axialSlice (a := a) (b := b) (B := B) u.gx_memL2
  have hfam : ∀ k : ℚ × ℚ × ℕ, ∀ᵐ z ∂(volume.restrict B),
      a < (k.1 : ℝ) → ((k.1 : ℝ) < (k.2.1 : ℝ)) → ((k.2.1 : ℝ) < b) →
        ∫ x in Ioo a b, (u.toFun (x, z) - ∫ t in ((a + b) / 2)..x, u.gx (t, z)) *
          (idxBump k x - (∫ y, idxBump k y) * RobinCaps.Sobolev.bump hab x) = 0 := by
    intro k
    by_cases hk : a < (k.1 : ℝ) ∧ ((k.1 : ℝ) < (k.2.1 : ℝ)) ∧ ((k.2.1 : ℝ) < b)
    · obtain ⟨h1, h2, h3⟩ := hk
      have hφ : ContDiff ℝ ∞ (idxBump k) := idxBump_contDiff h2
      have hφc : HasCompactSupport (idxBump k) := idxBump_hasCompactSupport h2
      have hφs : tsupport (idxBump k) ⊆ Ioo a b := by
        rw [idxBump_tsupport h2]; exact Icc_subset_Ioo h1 h3
      have hρsmooth : ContDiff ℝ ∞ (RobinCaps.Sobolev.bump hab) :=
        RobinCaps.Sobolev.bump_contDiff hab
      have hρc : HasCompactSupport (RobinCaps.Sobolev.bump hab) :=
        RobinCaps.Sobolev.bump_hasCompactSupport hab
      have hρs : tsupport (RobinCaps.Sobolev.bump hab) ⊆ Ioo a b :=
        RobinCaps.Sobolev.bump_tsupport hab
      have hψ : ContDiff ℝ ∞ (fun x => idxBump k x
          - (∫ y, idxBump k y) * RobinCaps.Sobolev.bump hab x) :=
        hφ.sub (contDiff_const.mul hρsmooth)
      have hψc : HasCompactSupport (fun x => idxBump k x
          - (∫ y, idxBump k y) * RobinCaps.Sobolev.bump hab x) :=
        IsCompact.of_isClosed_subset (IsCompact.union hφc hρc) isClosed_closure
          (tsupport_sub_const_mul_subset _ _ _)
      have hψs : tsupport (fun x => idxBump k x
          - (∫ y, idxBump k y) * RobinCaps.Sobolev.bump hab x) ⊆ Ioo a b :=
        (tsupport_sub_const_mul_subset _ _ _).trans (union_subset hφs hρs)
      have hψ0 : ∫ x, (idxBump k x - (∫ y, idxBump k y) * RobinCaps.Sobolev.bump hab x) = 0 := by
        rw [integral_sub (hφ.continuous.integrable_of_hasCompactSupport hφc)
          ((hρsmooth.continuous.integrable_of_hasCompactSupport hρc).const_mul _),
          integral_const_mul, RobinCaps.Sobolev.bump_integral hab, mul_one, sub_self]
      obtain ⟨Ψ, hΨ, hΨc, hΨs, hΨd⟩ :=
        RobinCaps.Sobolev.exists_test_primitive hab hψ hψc hψs hψ0
      have hdΨ : ∀ x : ℝ, deriv Ψ x
          = idxBump k x - (∫ y, idxBump k y) * RobinCaps.Sobolev.bump hab x := by
        intro x; rw [hΨd]
      have hΨ' : ContDiff ℝ ∞ (deriv Ψ) := (contDiff_infty_iff_deriv.1 hΨ).2
      filter_upwards [sliceAxial_of_test hB u hΨ hΨc hΨs, hu, hgx] with z hz hz1 hz2
      intro _ _ _
      have i1 : IntegrableOn (fun x => u.toFun (x, z) * deriv Ψ x) (Ioo a b) :=
        RobinCaps.Sobolev.integrableOn_mul_test hz1.1 hΨ'.continuous hΨc.deriv
      have i2 : IntegrableOn (fun x => u.gx (x, z) * Ψ x) (Ioo a b) :=
        RobinCaps.Sobolev.integrableOn_mul_test hz2.1 hΨ.continuous hΨc
      have i3 : IntegrableOn
          (fun x => (∫ t in ((a + b) / 2)..x, u.gx (t, z)) * deriv Ψ x) (Ioo a b) :=
        RobinCaps.Sobolev.integrableOn_mul_test (integrableOn_primitive hab hz2.1)
          hΨ'.continuous hΨc.deriv
      have hsplit : (∫ x in Ioo a b, (u.toFun (x, z) * deriv Ψ x + u.gx (x, z) * Ψ x))
          = (∫ x in Ioo a b, u.toFun (x, z) * deriv Ψ x)
            + ∫ x in Ioo a b, u.gx (x, z) * Ψ x := integral_add i1 i2
      have hprim := RobinCaps.Sobolev.hasWeakDeriv_primitive hab hz2.1 hmid Ψ hΨ hΨc hΨs
      calc ∫ x in Ioo a b, (u.toFun (x, z) - ∫ t in ((a + b) / 2)..x, u.gx (t, z)) *
              (idxBump k x - (∫ y, idxBump k y) * RobinCaps.Sobolev.bump hab x)
          = ∫ x in Ioo a b, (u.toFun (x, z) - ∫ t in ((a + b) / 2)..x, u.gx (t, z))
              * deriv Ψ x := integral_congr_ae (.of_forall fun x => by simp only [hdΨ])
        _ = (∫ x in Ioo a b, u.toFun (x, z) * deriv Ψ x)
              - ∫ x in Ioo a b, (∫ t in ((a + b) / 2)..x, u.gx (t, z)) * deriv Ψ x := by
              rw [← integral_sub i1 i3]
              exact integral_congr_ae (.of_forall fun x => by ring)
        _ = 0 := by rw [hprim]; rw [hsplit] at hz; linarith
    · filter_upwards with z
      intro h1 h2 h3
      exact absurd ⟨h1, h2, h3⟩ hk
  have hall : ∀ᵐ z ∂(volume.restrict B), ∀ k : ℚ × ℚ × ℕ,
      a < (k.1 : ℝ) → ((k.1 : ℝ) < (k.2.1 : ℝ)) → ((k.2.1 : ℝ) < b) →
        ∫ x in Ioo a b, (u.toFun (x, z) - ∫ t in ((a + b) / 2)..x, u.gx (t, z)) *
          (idxBump k x - (∫ y, idxBump k y) * RobinCaps.Sobolev.bump hab x) = 0 :=
    ae_all_iff.2 hfam
  filter_upwards [hall, hu, hgx] with z hz hz1 hz2
  exact hasWeakDeriv_of_idxBump hab hz1.1 hz2.1 hz

/-- **The `SliceACLAxial` target for the cylinder.**  Note that for `z ∉ B` the axial slice of
`Ω` is empty and the identity is trivially true, so the statement holds for almost every
`z : EuclideanSpace ℝ (Fin m)` with respect to the *full* volume. -/
theorem sliceACLAxial_prod (hab : a < b) (hB : IsOpen B) (u : H1P (Ioo a b ×ˢ B)) :
    SliceACLAxial (Ioo a b ×ˢ B) u := by
  have h := sliceACL_axial hab hB u
  rw [ae_restrict_iff' hB.measurableSet] at h
  filter_upwards [h] with z hz
  intro φ hφ hφc hφs
  by_cases hzB : z ∈ B
  · have hslice : {x : ℝ | (x, z) ∈ Ioo a b ×ˢ B} = Ioo a b := by
      ext x; simp [hzB]
    rw [hslice] at hφs ⊢
    exact hz hzB φ hφ hφc hφs
  · have hslice : {x : ℝ | (x, z) ∈ Ioo a b ×ˢ B} = (∅ : Set ℝ) := by
      ext x; simp [hzB]
    rw [hslice]
    simp

/-- **The absolutely continuous representative on almost every axial line.**  Stated on the
cylinder `(0,ℓ) × B` (which is the shape the trace argument uses), so that no translation of
the interval is needed. -/
theorem sliceACL_axial_h1 {ℓ : ℝ} (hℓ : 0 < ℓ) (hB : IsOpen B) (u : H1P (Ioo 0 ℓ ×ˢ B)) :
    ∀ᵐ z ∂(volume.restrict B), ∃ w : RobinCaps.Sobolev.H1 ℓ,
      w.toFun =ᵐ[volume.restrict (Ioo 0 ℓ)] (fun x => u.toFun (x, z)) ∧
      deriv w.toFun =ᵐ[volume.restrict (Ioo 0 ℓ)] (fun x => u.gx (x, z)) := by
  filter_upwards [sliceACL_axial hℓ hB u,
    ae_integrableOn_axialSlice (a := 0) (b := ℓ) (B := B) u.memL2,
    ae_integrableOn_axialSlice (a := 0) (b := ℓ) (B := B) u.gx_memL2] with z hz hz1 hz2
  exact RobinCaps.Sobolev.exists_h1_of_hasWeakDeriv hℓ hz1.1 hz2.1 hz2.2 hz

/-! ### Deliverable 3: the transverse ACL property

The transverse analogue of `sliceACL_axial` cannot use the du Bois-Reymond trick: on
`EuclideanSpace ℝ (Fin m)` with `m ≥ 2` the identity "for all test functions" is not equivalent
to an a.e. pointwise formula (that would make `u(x,·)` a potential of `∇_z u(x,·)`, which needs
integration along paths).  The route used here instead is **separability of `L²(B)`**: the
pairs `(∂ᵢχ, χ) ∈ L²(B) × L²(B)` indexed by the test functions `χ` form a subset of a
second-countable metric space (`MeasureTheory.Lp.SecondCountableTopology`), hence admit a
*countable* dense subset (`IsSeparable.exists_countable_dense_subset`); the pairing
`(v, g) ↦ ∫_B (v ∂ᵢχ + gᵢ χ)` is Lipschitz in that pair by Cauchy-Schwarz
(`abs_integral_mul_sub_le`), uniformly for the slices `(u(x,·), ∇_zu(x,·))`, which lie in
`L²(B)` for a.e. `x` (`ae_memLp_transverseSlice`).  One countable intersection of null sets
therefore suffices. -/

/-- For almost every axial coordinate `x` in `(a,b)`, the transverse slice `z ↦ u(x,z)` has
`z ↦ (∇_z u)(x,z)` as a weak gradient on `B`.  Proved in `sliceACL_transverse` below. -/
def SliceACLTransverse (a b : ℝ) (B : Set (EuclideanSpace ℝ (Fin m)))
    (u : H1P (Ioo a b ×ˢ B)) : Prop :=
  ∀ᵐ x ∂(volume.restrict (Ioo a b)),
    RobinCaps.Sobolev.Weak.HasWeakGrad B (fun z => u.toFun (x, z)) (fun z => u.gz (x, z))

/-- `SliceACLTransverse` is exactly what the `SliceACL` target of
`RobinCaps/ThinDomain/H1P.lean` needs on the cylinder: outside `(a,b)` the transverse slice of
the cylinder is empty, where the weak-gradient identity holds trivially. -/
theorem sliceACL_of_transverse (u : H1P (Ioo a b ×ˢ B)) (h : SliceACLTransverse a b B u) :
    SliceACL (Ioo a b ×ˢ B) u := by
  rw [SliceACLTransverse, ae_restrict_iff' measurableSet_Ioo] at h
  filter_upwards [h] with x hx
  by_cases hxI : x ∈ Ioo a b
  · have hslice : {z : EuclideanSpace ℝ (Fin m) | (x, z) ∈ Ioo a b ×ˢ B} = B := by
      ext z; simp [hxI]
    rw [hslice]
    exact hx hxI
  · have hslice : {z : EuclideanSpace ℝ (Fin m) | (x, z) ∈ Ioo a b ×ˢ B}
        = (∅ : Set (EuclideanSpace ℝ (Fin m))) := by
      ext z; simp [hxI]
    rw [hslice]
    intro φ hφ hφc hφs i
    simp

/-! ### `L²` pairings, for the transverse upgrade -/

section L2Pairing

variable {α : Type*} [MeasurableSpace α] {ν : Measure α}

/-- Cauchy-Schwarz for the pairing of an `L²` function with an element of `L²`. -/
theorem abs_integral_mul_le_norm {v : α → ℝ} (hv : MemLp v 2 ν) (W : Lp ℝ 2 ν) :
    |∫ z, v z * W z ∂ν| ≤ ‖hv.toLp v‖ * ‖W‖ := by
  have h : (∫ z, v z * W z ∂ν) = inner ℝ (hv.toLp v) W := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hv.coeFn_toLp] with z hz
    rw [hz]
    simp [RCLike.inner_apply, mul_comm]
  rw [h]
  exact abs_real_inner_le_norm _ _

/-- The pairing of a fixed `L²` function with an element of `L²` is Lipschitz. -/
theorem abs_integral_mul_sub_le {v : α → ℝ} (hv : MemLp v 2 ν) (A A' : Lp ℝ 2 ν) :
    |(∫ z, v z * A z ∂ν) - ∫ z, v z * A' z ∂ν| ≤ ‖hv.toLp v‖ * ‖A - A'‖ := by
  have hint : ∀ W : Lp ℝ 2 ν, Integrable (fun z => v z * W z) ν := fun W =>
    hv.integrable_mul (Lp.memLp W)
  rw [← integral_sub (hint A) (hint A')]
  have h1 : (∫ z, (v z * A z - v z * A' z) ∂ν) = ∫ z, v z * ((A - A' : Lp ℝ 2 ν) z) ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub A A'] with z hz
    rw [hz]
    simp [mul_sub]
  rw [h1]
  exact abs_integral_mul_le_norm hv (A - A')

end L2Pairing

/-- Almost every transverse slice of an `L²(Ω)` function is in `L²(B)`. -/
theorem ae_memLp_transverseSlice {f : CapSpace m → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo a b ×ˢ B))) :
    ∀ᵐ x ∂(volume.restrict (Ioo a b)), MemLp (fun z => f (x, z)) 2 (volume.restrict B) := by
  have hsq : Integrable (fun p => f p ^ 2) (volume.restrict (Ioo a b ×ˢ B)) := hf.integrable_sq
  have hmeas : AEStronglyMeasurable f (volume.restrict (Ioo a b ×ˢ B)) := hf.aestronglyMeasurable
  rw [restrict_prodDomain] at hsq hmeas
  filter_upwards [hsq.prod_right_ae, hmeas.prodMk_left] with x h1 h2
  exact (memLp_two_iff_integrable_sq h2).2 h1

/-- **Deliverable 3 (ACL in the transverse direction).**  For almost every axial coordinate
`x ∈ (a,b)`, the transverse slice `z ↦ u(x,z)` has `z ↦ (∇_z u)(x,z)` as a weak gradient on
`B`.

The exceptional null set is made independent of the test function by separability of
`L²(B)`: the pairs `(∂ᵢχ, χ)` of test data form a subset of `L²(B) × L²(B)`, which is a
second-countable metric space, hence has a *countable* dense subset; the pairing
`(v, g) ↦ ∫_B (v ∂ᵢχ + gᵢ χ)` is Lipschitz in that pair by Cauchy-Schwarz, uniformly for
slices `(u(x,·), ∇_zu(x,·)) ∈ L²(B)` (which is the case for a.e. `x`). -/
theorem sliceACL_transverse (u : H1P (Ioo a b ×ˢ B)) : SliceACLTransverse a b B u := by
  haveI : Fact ((2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨by simp⟩
  haveI : IsFiniteMeasureOnCompacts ((volume : Measure (EuclideanSpace ℝ (Fin m))).restrict B) :=
    ⟨fun K hK => lt_of_le_of_lt (Measure.restrict_le_self _) hK.measure_lt_top⟩
  haveI hsc : SecondCountableTopology
      (Lp ℝ 2 ((volume : Measure (EuclideanSpace ℝ (Fin m))).restrict B)) := inferInstance
  have hU := ae_memLp_transverseSlice (a := a) (b := b) (B := B) u.memL2
  have main : ∀ i : Fin m, ∀ᵐ x ∂(volume.restrict (Ioo a b)),
      ∀ χ : EuclideanSpace ℝ (Fin m) → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
        tsupport χ ⊆ B →
        ∫ z in B, u.toFun (x, z) * fderiv ℝ χ z (EuclideanSpace.single i 1)
          = - ∫ z in B, u.gz (x, z) i * χ z := by
    intro i
    have hG := ae_memLp_transverseSlice (a := a) (b := b) (B := B)
      (memLp_two_compP u.gz_memL2 i)
    set S : Set (Lp ℝ 2 ((volume : Measure (EuclideanSpace ℝ (Fin m))).restrict B) ×
        Lp ℝ 2 ((volume : Measure (EuclideanSpace ℝ (Fin m))).restrict B)) :=
      {P | ∃ χ : EuclideanSpace ℝ (Fin m) → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
        tsupport χ ⊆ B ∧
        (⇑P.1 =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin m))).restrict B]
          fun z => fderiv ℝ χ z (EuclideanSpace.single i 1)) ∧
        (⇑P.2 =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin m))).restrict B] χ)} with hSdef
    obtain ⟨C, hCS, hCc, hCd⟩ := (TopologicalSpace.IsSeparable.of_separableSpace S).exists_countable_dense_subset
    have hQC : ∀ P ∈ C, ∀ᵐ x ∂(volume.restrict (Ioo a b)),
        ∫ z in B, (u.toFun (x, z) * P.1 z + u.gz (x, z) i * P.2 z) = 0 := by
      intro P hP
      obtain ⟨χ, hχ, hχc, hχs, hP1, hP2⟩ := hSdef ▸ hCS hP
      filter_upwards [sliceTransverse_of_test u hχ hχc hχs i] with x hx
      rw [← hx]
      refine integral_congr_ae ?_
      filter_upwards [hP1, hP2] with z hz1 hz2
      rw [hz1, hz2]
    have hall := (ae_ball_iff hCc).2 hQC
    filter_upwards [hall, hU, hG] with x hx hUx hGx
    intro χ hχ hχc hχs
    have hAmem : MemLp (fun z => fderiv ℝ χ z (EuclideanSpace.single i 1)) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin m))).restrict B) :=
      Continuous.memLp_of_hasCompactSupport
        ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
        (hχc.fderiv_apply ℝ _)
    have hBmem : MemLp χ 2 ((volume : Measure (EuclideanSpace ℝ (Fin m))).restrict B) :=
      hχ.continuous.memLp_of_hasCompactSupport hχc
    obtain ⟨A, hA⟩ : ∃ A : Lp ℝ 2 ((volume : Measure (EuclideanSpace ℝ (Fin m))).restrict B),
        ⇑A =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin m))).restrict B]
          fun z => fderiv ℝ χ z (EuclideanSpace.single i 1) :=
      ⟨hAmem.toLp _, hAmem.coeFn_toLp⟩
    obtain ⟨D, hD⟩ : ∃ D : Lp ℝ 2 ((volume : Measure (EuclideanSpace ℝ (Fin m))).restrict B),
        ⇑D =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin m))).restrict B] χ :=
      ⟨hBmem.toLp _, hBmem.coeFn_toLp⟩
    have hP₀ : ((A, D) :
        Lp ℝ 2 ((volume : Measure (EuclideanSpace ℝ (Fin m))).restrict B) ×
          Lp ℝ 2 ((volume : Measure (EuclideanSpace ℝ (Fin m))).restrict B)) ∈ S := by
      rw [hSdef]
      exact ⟨χ, hχ, hχc, hχs, hA, hD⟩
    have hTadd : ∀ P Q : Lp ℝ 2 ((volume : Measure (EuclideanSpace ℝ (Fin m))).restrict B),
        (∫ z in B, (u.toFun (x, z) * P z + u.gz (x, z) i * Q z))
          = (∫ z in B, u.toFun (x, z) * P z) + ∫ z in B, u.gz (x, z) i * Q z := fun P Q =>
      integral_add (hUx.integrable_mul (Lp.memLp P)) (hGx.integrable_mul (Lp.memLp Q))
    have hkey : ∀ ε > 0,
        |(∫ z in B, u.toFun (x, z) * A z) + ∫ z in B, u.gz (x, z) i * D z|
          ≤ (‖hUx.toLp _‖ + ‖hGx.toLp _‖) * ε := by
      intro ε hε
      obtain ⟨P, hPC, hPd⟩ := Metric.mem_closure_iff.1 (hCd hP₀) ε hε
      have h0 : (∫ z in B, u.toFun (x, z) * P.1 z) + ∫ z in B, u.gz (x, z) i * P.2 z = 0 := by
        rw [← hTadd]; exact hx P hPC
      have hdd : dist ((A, D) : Lp ℝ 2 ((volume : Measure (EuclideanSpace ℝ (Fin m))).restrict B) ×
          Lp ℝ 2 ((volume : Measure (EuclideanSpace ℝ (Fin m))).restrict B)) P
          = max (dist A P.1) (dist D P.2) := Prod.dist_eq
      have hd1 : ‖A - P.1‖ ≤ ε := by
        rw [← dist_eq_norm]
        have hle : dist A P.1 ≤ dist ((A, D) : _ × _) P := by rw [hdd]; exact le_max_left _ _
        linarith
      have hd2 : ‖D - P.2‖ ≤ ε := by
        rw [← dist_eq_norm]
        have hle : dist D P.2 ≤ dist ((A, D) : _ × _) P := by rw [hdd]; exact le_max_right _ _
        linarith
      calc |(∫ z in B, u.toFun (x, z) * A z) + ∫ z in B, u.gz (x, z) i * D z|
          = |((∫ z in B, u.toFun (x, z) * A z) - ∫ z in B, u.toFun (x, z) * P.1 z)
              + ((∫ z in B, u.gz (x, z) i * D z) - ∫ z in B, u.gz (x, z) i * P.2 z)| := by
            congr 1; linarith
        _ ≤ |(∫ z in B, u.toFun (x, z) * A z) - ∫ z in B, u.toFun (x, z) * P.1 z|
              + |(∫ z in B, u.gz (x, z) i * D z) - ∫ z in B, u.gz (x, z) i * P.2 z| :=
            abs_add_le _ _
        _ ≤ ‖hUx.toLp _‖ * ‖A - P.1‖ + ‖hGx.toLp _‖ * ‖D - P.2‖ :=
            add_le_add (abs_integral_mul_sub_le hUx A P.1) (abs_integral_mul_sub_le hGx D P.2)
        _ ≤ ‖hUx.toLp _‖ * ε + ‖hGx.toLp _‖ * ε :=
            add_le_add (mul_le_mul_of_nonneg_left hd1 (norm_nonneg _))
              (mul_le_mul_of_nonneg_left hd2 (norm_nonneg _))
        _ = (‖hUx.toLp _‖ + ‖hGx.toLp _‖) * ε := by ring
    have hTzero : (∫ z in B, u.toFun (x, z) * A z) + ∫ z in B, u.gz (x, z) i * D z = 0 := by
      refine abs_nonpos_iff.1 (le_of_forall_pos_le_add fun δ hδ => ?_)
      have hKpos : (0 : ℝ) < ‖hUx.toLp _‖ + ‖hGx.toLp _‖ + 1 := by positivity
      have h1 := hkey (δ / (‖hUx.toLp _‖ + ‖hGx.toLp _‖ + 1)) (by positivity)
      have h2 : (‖hUx.toLp _‖ + ‖hGx.toLp _‖) * (δ / (‖hUx.toLp _‖ + ‖hGx.toLp _‖ + 1)) ≤ δ := by
        rw [mul_div_assoc', div_le_iff₀ hKpos]
        nlinarith [norm_nonneg (hUx.toLp (fun z => u.toFun (x, z))),
          norm_nonneg (hGx.toLp (fun z => u.gz (x, z) i))]
      linarith
    have hAeq : (∫ z in B, u.toFun (x, z) * A z)
        = ∫ z in B, u.toFun (x, z) * fderiv ℝ χ z (EuclideanSpace.single i 1) := by
      refine integral_congr_ae ?_
      filter_upwards [hA] with z hz
      rw [hz]
    have hDeq : (∫ z in B, u.gz (x, z) i * D z) = ∫ z in B, u.gz (x, z) i * χ z := by
      refine integral_congr_ae ?_
      filter_upwards [hD] with z hz
      rw [hz]
    rw [hAeq, hDeq] at hTzero
    linarith
  filter_upwards [ae_all_iff.2 main] with x hx
  intro φ hφ hφc hφs i
  exact hx i φ hφ hφc hφs

/-- **The `SliceACL` target for the cylinder.**  Almost every transverse slice of an element of
`H1P ((a,b) × B)` has the corresponding slice of `∇_z u` as a weak gradient. -/
theorem sliceACL_prod (u : H1P (Ioo a b ×ˢ B)) : SliceACL (Ioo a b ×ˢ B) u :=
  sliceACL_of_transverse u (sliceACL_transverse u)

end

end RobinCaps.ThinDomain
