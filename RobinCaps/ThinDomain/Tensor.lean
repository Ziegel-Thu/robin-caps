import Mathlib
import RobinCaps.ThinDomain.H1P
import RobinCaps.ThinDomain.GroundState

/-!
# Tensor (separated) trial functions on the bulk cylinder

This file formalizes the trial functions of `eq:trial-extension` / `sec:proof` (upper bound) of
the manuscript: on the bulk cylinder

`Ω = I ×ˢ B`,  `I = Ioo a b ⊆ ℝ`,  `B = B_m(R) = Metric.ball 0 R ⊆ ℝ^m`,

a `C¹` axial profile `F : ℝ → ℝ` and a transverse state `ψ ∈ H¹(B)` (an element of
`TransH1 m R = Weak.H1 (transverseBall m R)`) are combined into

`(x, z) ↦ F x · ψ z`.

## Contents

* `bulkCyl a b m R` — the open cylinder `Ioo a b ×ˢ transverseBall m R ⊆ CapSpace m`, together
  with `isOpen_bulkCyl` and `volume_restrict_bulkCyl`
  (`volume.restrict Ω = (volume.restrict I).prod (volume.restrict B)`, the Fubini form used
  throughout).
* Slice lemmas for test functions: `hasCompactSupport_sliceSnd`, `tsupport_sliceSnd_subset`,
  `hasCompactSupport_sliceFst`, `tsupport_sliceFst_subset`, and the two chain-rule identities
  `hasDerivAt_sliceFst` and `fderiv_sliceSnd`.
* `integral_mul_deriv_eq_neg_of_compactSupport` and `setIntegral_mul_deriv_eq_neg` — the
  classical one-dimensional integration by parts against a compactly supported factor, deduced
  from `RobinCaps.ThinDomain.integral_deriv_eq_zero_of_compactSupport`.
* `memLp_two_tensor`, `memLp_two_tensor_vec` — `L²(Ω)` membership of `(x,z) ↦ f x · w z` and of
  `(x,z) ↦ f x • w z` for `f` continuous and `w ∈ L²(B)`.
* `tensorFun F ψ` and the main theorem **`hasWeakGradP_tensor`**: the weak gradient of
  `F ⊗ ψ` on `Ω` is `(F' ⊗ ψ, F ⊗ ∇ψ)`.  The axial identity is Fubini (`z` outer) plus the
  one-dimensional integration by parts on each line; the transverse identity is Fubini
  (`x` outer) plus `ψ.hasWeakGrad` applied to the smooth compactly supported slice `φ(x, ·)`.
* `H1P.tensor` — the resulting element of `H1P Ω`.
* **Factorisation of the two forms**: `massP_tensor` and `dirichletP_tensor`,

  `N_Ω[F ⊗ ψ] = (∫_I F²) · N_B[ψ]`,
  `D_Ω[F ⊗ ψ] = (∫_I F'²) · N_B[ψ] + (∫_I F²) · D_B[ψ]`,

  together with the normalised corollaries `massP_tensor_groundState` and
  `dirichletP_tensor_groundState` for `ψ = gs.psi` (where `NB gs.psi = 1`).

Everything is proved without `sorry`, `axiom` or `admit`.
-/

open MeasureTheory Set Filter

open scoped ContDiff ENNReal Topology

namespace RobinCaps.ThinDomain

open RobinCaps.Sobolev

noncomputable section

variable {m : ℕ} {a b R : ℝ}

/-! ### The bulk cylinder -/

/-- The **bulk cylinder** `Ω = Ioo a b ×ˢ B_m(R) ⊆ CapSpace m` of `sec:proof`. -/
def bulkCyl (a b : ℝ) (m : ℕ) (R : ℝ) : Set (CapSpace m) :=
  Set.Ioo a b ×ˢ transverseBall m R

theorem bulkCyl_eq : bulkCyl a b m R = Set.Ioo a b ×ˢ transverseBall m R := rfl

/-- The bulk cylinder is open. -/
theorem isOpen_bulkCyl : IsOpen (bulkCyl a b m R) :=
  isOpen_Ioo.prod Metric.isOpen_ball

theorem mem_bulkCyl_iff {p : CapSpace m} :
    p ∈ bulkCyl a b m R ↔ p.1 ∈ Set.Ioo a b ∧ p.2 ∈ transverseBall m R := Iff.rfl

/-- **The Fubini form of the volume on the cylinder.**  `Measure.volume_eq_prod` is definitional
on `ℝ × EuclideanSpace ℝ (Fin m)`, so restricting to a product set is exactly the product of the
restricted measures. -/
theorem volume_restrict_bulkCyl :
    (volume : Measure (CapSpace m)).restrict (bulkCyl a b m R)
      = ((volume : Measure ℝ).restrict (Set.Ioo a b)).prod
          ((volume : Measure (EuclideanSpace ℝ (Fin m))).restrict (transverseBall m R)) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  rfl

/-! ### Slices of test functions -/

section Slices

variable {φ : CapSpace m → ℝ}

/-- The transverse slice of a compactly supported function is compactly supported. -/
theorem hasCompactSupport_sliceSnd (hφc : HasCompactSupport φ) (x : ℝ) :
    HasCompactSupport (fun z : EuclideanSpace ℝ (Fin m) => φ (x, z)) := by
  have hK : IsCompact (tsupport φ) := hφc
  refine HasCompactSupport.intro (hK.image continuous_snd) ?_
  intro z hz
  exact image_eq_zero_of_notMem_tsupport fun hmem => hz ⟨(x, z), hmem, rfl⟩

/-- The axial slice of a compactly supported function is compactly supported. -/
theorem hasCompactSupport_sliceFst (hφc : HasCompactSupport φ)
    (z : EuclideanSpace ℝ (Fin m)) : HasCompactSupport (fun x : ℝ => φ (x, z)) := by
  have hK : IsCompact (tsupport φ) := hφc
  refine HasCompactSupport.intro (hK.image continuous_fst) ?_
  intro x hx
  exact image_eq_zero_of_notMem_tsupport fun hmem => hx ⟨(x, z), hmem, rfl⟩

/-- The closed support of a transverse slice is contained in the slice of the closed support. -/
theorem tsupport_sliceSnd_subset (φ : CapSpace m → ℝ) (x : ℝ) :
    tsupport (fun z : EuclideanSpace ℝ (Fin m) => φ (x, z))
      ⊆ {z : EuclideanSpace ℝ (Fin m) | (x, z) ∈ tsupport φ} := by
  refine closure_minimal (fun z hz => subset_tsupport φ (show (x, z) ∈ Function.support φ from hz))
    ?_
  exact IsClosed.preimage (f := fun z : EuclideanSpace ℝ (Fin m) => ((x, z) : CapSpace m))
    (continuous_const.prodMk continuous_id) (isClosed_tsupport φ)

/-- The closed support of an axial slice is contained in the slice of the closed support. -/
theorem tsupport_sliceFst_subset (φ : CapSpace m → ℝ) (z : EuclideanSpace ℝ (Fin m)) :
    tsupport (fun x : ℝ => φ (x, z)) ⊆ {x : ℝ | (x, z) ∈ tsupport φ} := by
  refine closure_minimal (fun x hx => subset_tsupport φ (show (x, z) ∈ Function.support φ from hx))
    ?_
  exact IsClosed.preimage (f := fun x : ℝ => ((x, z) : CapSpace m))
    (continuous_id.prodMk continuous_const) (isClosed_tsupport φ)

/-- A test function supported in the cylinder has all its transverse slices supported in the
ball. -/
theorem tsupport_sliceSnd_subset_ball (hφs : tsupport φ ⊆ bulkCyl a b m R) (x : ℝ) :
    tsupport (fun z : EuclideanSpace ℝ (Fin m) => φ (x, z)) ⊆ transverseBall m R :=
  (tsupport_sliceSnd_subset φ x).trans fun _ hz => (hφs hz).2

/-- A test function supported in the cylinder has all its axial slices supported in the
interval. -/
theorem tsupport_sliceFst_subset_interval (hφs : tsupport φ ⊆ bulkCyl a b m R)
    (z : EuclideanSpace ℝ (Fin m)) :
    tsupport (fun x : ℝ => φ (x, z)) ⊆ Set.Ioo a b :=
  (tsupport_sliceFst_subset φ z).trans fun _ hx => (hφs hx).1

/-- **Chain rule, axial direction**: the derivative of the axial slice is the axial partial
derivative. -/
theorem hasDerivAt_sliceFst (hφ : ContDiff ℝ 1 φ) (x : ℝ) (z : EuclideanSpace ℝ (Fin m)) :
    HasDerivAt (fun t : ℝ => φ (t, z))
      (fderiv ℝ φ (x, z) ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m)))) x := by
  have h1 : HasDerivAt (fun t : ℝ => ((t, z) : CapSpace m))
      ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x z)
  have h2 := (hφ.differentiable le_rfl (x, z)).hasFDerivAt.comp_hasDerivAt x h1
  simpa [Function.comp_def] using h2

theorem deriv_sliceFst (hφ : ContDiff ℝ 1 φ) (x : ℝ) (z : EuclideanSpace ℝ (Fin m)) :
    deriv (fun t : ℝ => φ (t, z)) x
      = fderiv ℝ φ (x, z) ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))) :=
  (hasDerivAt_sliceFst hφ x z).deriv

/-- **Chain rule, transverse directions**: the Fréchet derivative of the transverse slice is the
transverse part of the Fréchet derivative. -/
theorem fderiv_sliceSnd (hφ : ContDiff ℝ 1 φ) (x : ℝ) (z v : EuclideanSpace ℝ (Fin m)) :
    fderiv ℝ (fun w : EuclideanSpace ℝ (Fin m) => φ (x, w)) z v
      = fderiv ℝ φ (x, z) ((0 : ℝ), v) := by
  have h1 : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin m) => ((x, w) : CapSpace m))
      (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin m))) z :=
    hasFDerivAt_prodMk_right x z
  have h2 : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin m) => φ (x, w))
      ((fderiv ℝ φ (x, z)).comp
        (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin m)))) z :=
    (hφ.differentiable le_rfl (x, z)).hasFDerivAt.comp z h1
  rw [h2.fderiv]
  rfl

end Slices

/-! ### One-dimensional integration by parts against a compactly supported factor -/

/-- **Integration by parts on `ℝ`**: for `F` of class `C¹` and `g` of class `C¹` with compact
support, `∫ F g' = - ∫ F' g`.  No support assumption on `F` is needed: `g` carries it. -/
theorem integral_mul_deriv_eq_neg_of_compactSupport {F g : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) :
    ∫ x, F x * deriv g x = - ∫ x, deriv F x * g x := by
  have hFd : ∀ x, HasDerivAt F (deriv F x) x := fun x =>
    (hF.differentiable le_rfl x).hasDerivAt
  have hgd : ∀ x, HasDerivAt g (deriv g x) x := fun x =>
    (hg.differentiable le_rfl x).hasDerivAt
  have hprod : ∀ x, HasDerivAt (fun t => F t * g t) (deriv F x * g x + F x * deriv g x) x :=
    fun x => (hFd x).mul (hgd x)
  have hF' : Continuous (deriv F) := hF.continuous_deriv le_rfl
  have hg' : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hcont : Continuous fun x => deriv F x * g x + F x * deriv g x :=
    (hF'.mul hg.continuous).add (hF.continuous.mul hg')
  have hsupp : HasCompactSupport fun t => F t * g t := hgc.mul_left
  have h0 := integral_deriv_eq_zero_of_compactSupport hprod hcont hsupp
  have h1 : Integrable fun x => deriv F x * g x :=
    Continuous.integrable_of_hasCompactSupport (hF'.mul hg.continuous) hgc.mul_left
  have h2 : Integrable fun x => F x * deriv g x :=
    Continuous.integrable_of_hasCompactSupport (hF.continuous.mul hg') hgc.deriv.mul_left
  rw [integral_add h1 h2] at h0
  linarith

/-- The same identity over any set containing the support of `g`. -/
theorem setIntegral_mul_deriv_eq_neg {F g : ℝ → ℝ} {S : Set ℝ} (hF : ContDiff ℝ 1 F)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (hS : tsupport g ⊆ S) :
    ∫ x in S, F x * deriv g x = - ∫ x in S, deriv F x * g x := by
  have e1 : (∫ x in S, F x * deriv g x) = ∫ x, F x * deriv g x := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro x hx
    have hnot : x ∉ tsupport g := fun h => hx (hS h)
    have : deriv g x = 0 :=
      Function.notMem_support.1 fun h => hnot (support_deriv_subset h)
    rw [this, mul_zero]
  have e2 : (∫ x in S, deriv F x * g x) = ∫ x, deriv F x * g x := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport fun h => hx (hS h), mul_zero]
  rw [e1, e2]
  exact integral_mul_deriv_eq_neg_of_compactSupport hF hg hgc

/-! ### `L²` membership of tensor products -/

/-- The square of a continuous function is integrable on a bounded interval. -/
theorem integrable_sq_on_Ioo {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable (fun x => f x ^ 2) (volume.restrict (Set.Ioo a b)) :=
  IntegrableOn.mono_set ((hf.pow 2).integrableOn_Icc (a := a) (b := b))
    Set.Ioo_subset_Icc_self

/-- **`L²(Ω)` for a scalar tensor product.**  If `f` is continuous (hence bounded on the bounded
interval `I`) and `w ∈ L²(B)`, then `(x, z) ↦ f x · w z` is in `L²(Ω)`. -/
theorem memLp_two_tensor {f : ℝ → ℝ} (hf : Continuous f)
    {w : EuclideanSpace ℝ (Fin m) → ℝ}
    (hw : MemLp w 2 (volume.restrict (transverseBall m R))) :
    MemLp (fun p : CapSpace m => f p.1 * w p.2) 2 (volume.restrict (bulkCyl a b m R)) := by
  rw [volume_restrict_bulkCyl]
  have hm : AEStronglyMeasurable (fun p : CapSpace m => f p.1 * w p.2)
      (((volume : Measure ℝ).restrict (Set.Ioo a b)).prod
        ((volume : Measure (EuclideanSpace ℝ (Fin m))).restrict (transverseBall m R))) :=
    (hf.aestronglyMeasurable.comp_fst).mul (hw.aestronglyMeasurable.comp_snd)
  rw [memLp_two_iff_integrable_sq hm]
  have hprod := (integrable_sq_on_Ioo (a := a) (b := b) hf).mul_prod hw.integrable_sq
  refine hprod.congr (Filter.Eventually.of_forall fun p => ?_)
  simp [mul_pow]

/-- **`L²(Ω)` for a vector tensor product.**  If `f` is continuous and `w ∈ L²(B; ℝᵐ)`, then
`(x, z) ↦ f x • w z` is in `L²(Ω; ℝᵐ)`. -/
theorem memLp_two_tensor_vec {f : ℝ → ℝ} (hf : Continuous f)
    {w : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    (hw : MemLp w 2 (volume.restrict (transverseBall m R))) :
    MemLp (fun p : CapSpace m => f p.1 • w p.2) 2 (volume.restrict (bulkCyl a b m R)) := by
  rw [volume_restrict_bulkCyl]
  have hm : AEStronglyMeasurable (fun p : CapSpace m => f p.1 • w p.2)
      (((volume : Measure ℝ).restrict (Set.Ioo a b)).prod
        ((volume : Measure (EuclideanSpace ℝ (Fin m))).restrict (transverseBall m R))) :=
    (hf.aestronglyMeasurable.comp_fst).smul (hw.aestronglyMeasurable.comp_snd)
  rw [memLp_two_iff_integrable_sq_norm hm]
  have hwn : Integrable (fun z => ‖w z‖ ^ 2)
      (volume.restrict (transverseBall m R)) :=
    (memLp_two_iff_integrable_sq_norm hw.aestronglyMeasurable).1 hw
  have hprod := (integrable_sq_on_Ioo (a := a) (b := b) hf).mul_prod hwn
  refine hprod.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

/-! ### The tensor trial function and its weak gradient -/

/-- **The separated trial function** `(x, z) ↦ F x · ψ z` of `eq:trial-extension`. -/
def tensorFun (F : ℝ → ℝ) (ψ : TransH1 m R) (p : CapSpace m) : ℝ := F p.1 * ψ.toFun p.2

@[simp] theorem tensorFun_apply (F : ℝ → ℝ) (ψ : TransH1 m R) (p : CapSpace m) :
    tensorFun F ψ p = F p.1 * ψ.toFun p.2 := rfl

/-- **The weak gradient of a separated trial function.**

For `F` of class `C¹` and `ψ ∈ H¹(B_m(R))`, the function `F ⊗ ψ` has, on the bulk cylinder
`Ω = I ×ˢ B`, the weak gradient

`∂ₓ(F ⊗ ψ) = F' ⊗ ψ`,  `∇_z(F ⊗ ψ) = F ⊗ ∇ψ`.

The axial identity is Fubini (`z` outer, `x` inner) followed by the classical one-dimensional
integration by parts `setIntegral_mul_deriv_eq_neg` on each line `x ↦ F x · φ(x, z)`; the
transverse identity is Fubini (`x` outer, `z` inner) followed by `ψ.hasWeakGrad` applied to the
smooth compactly supported slice `φ(x, ·)`. -/
theorem hasWeakGradP_tensor (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) (ψ : TransH1 m R) :
    HasWeakGradP (bulkCyl a b m R) (tensorFun F ψ)
      (fun p => deriv F p.1 * ψ.toFun p.2) (fun p => F p.1 • ψ.grad p.2) := by
  have hmeas := volume_restrict_bulkCyl (a := a) (b := b) (m := m) (R := R)
  have hu : MemLp (tensorFun F ψ) 2 (volume.restrict (bulkCyl a b m R)) :=
    memLp_two_tensor hF.continuous ψ.memL2
  have hgx : MemLp (fun p : CapSpace m => deriv F p.1 * ψ.toFun p.2) 2
      (volume.restrict (bulkCyl a b m R)) :=
    memLp_two_tensor (hF.continuous_deriv le_rfl) ψ.memL2
  have hgz : MemLp (fun p : CapSpace m => F p.1 • ψ.grad p.2) 2
      (volume.restrict (bulkCyl a b m R)) :=
    memLp_two_tensor_vec hF.continuous ψ.grad_memL2
  intro φ hφ hφc hφs
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  constructor
  · -- axial identity
    have hintL : Integrable (fun p : CapSpace m => tensorFun F ψ p *
        fderiv ℝ φ p ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))))
        (volume.restrict (bulkCyl a b m R)) :=
      integrable_mul_dirDeriv hu hφ hφc _
    have hintR : Integrable
        (fun p : CapSpace m => (deriv F p.1 * ψ.toFun p.2) * φ p)
        (volume.restrict (bulkCyl a b m R)) :=
      integrable_gx_mul hgx hφ hφc
    rw [hmeas] at hintL hintR
    have key : ∀ z : EuclideanSpace ℝ (Fin m),
        (∫ x in Set.Ioo a b, tensorFun F ψ (x, z) *
            fderiv ℝ φ (x, z) ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))))
          = -∫ x in Set.Ioo a b, (deriv F x * ψ.toFun z) * φ (x, z) := by
      intro z
      have hgC : ContDiff ℝ 1 fun t : ℝ => φ (t, z) :=
        hφ1.comp (contDiff_id.prodMk contDiff_const)
      have hgc : HasCompactSupport fun t : ℝ => φ (t, z) := hasCompactSupport_sliceFst hφc z
      have hgs : tsupport (fun t : ℝ => φ (t, z)) ⊆ Set.Ioo a b :=
        tsupport_sliceFst_subset_interval hφs z
      have h1 : (∫ x in Set.Ioo a b, tensorFun F ψ (x, z) *
            fderiv ℝ φ (x, z) ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))))
          = ψ.toFun z * ∫ x in Set.Ioo a b, F x * deriv (fun t : ℝ => φ (t, z)) x := by
        rw [← integral_const_mul]
        refine integral_congr_ae (.of_forall fun x => ?_)
        simp only [tensorFun_apply, deriv_sliceFst hφ1 x z]
        ring
      have h2 : (∫ x in Set.Ioo a b, (deriv F x * ψ.toFun z) * φ (x, z))
          = ψ.toFun z * ∫ x in Set.Ioo a b, deriv F x * φ (x, z) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (.of_forall fun x => ?_)
        ring
      have hibp : (∫ x in Set.Ioo a b, F x * deriv (fun t : ℝ => φ (t, z)) x)
          = -∫ x in Set.Ioo a b, deriv F x * φ (x, z) :=
        setIntegral_mul_deriv_eq_neg hF hgC hgc hgs
      rw [h1, h2, hibp]
      ring
    calc (∫ p in bulkCyl a b m R, tensorFun F ψ p *
            fderiv ℝ φ p ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))))
        = ∫ z in transverseBall m R, ∫ x in Set.Ioo a b, tensorFun F ψ (x, z) *
            fderiv ℝ φ (x, z) ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))) := by
          rw [hmeas]; exact integral_prod_symm _ hintL
      _ = ∫ z in transverseBall m R,
            -∫ x in Set.Ioo a b, (deriv F x * ψ.toFun z) * φ (x, z) :=
          integral_congr_ae (.of_forall key)
      _ = -∫ z in transverseBall m R, ∫ x in Set.Ioo a b,
            (deriv F x * ψ.toFun z) * φ (x, z) := integral_neg _
      _ = -∫ p in bulkCyl a b m R, (deriv F p.1 * ψ.toFun p.2) * φ p := by
          rw [hmeas, integral_prod_symm _ hintR]
  · -- transverse identities
    intro i
    have hintL : Integrable (fun p : CapSpace m => tensorFun F ψ p *
        fderiv ℝ φ p ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)))
        (volume.restrict (bulkCyl a b m R)) :=
      integrable_mul_dirDeriv hu hφ hφc _
    have hintR : Integrable
        (fun p : CapSpace m => (F p.1 • ψ.grad p.2) i * φ p)
        (volume.restrict (bulkCyl a b m R)) :=
      integrable_compP_mul hgz hφ hφc i
    rw [hmeas] at hintL hintR
    have key : ∀ x : ℝ,
        (∫ z in transverseBall m R, tensorFun F ψ (x, z) *
            fderiv ℝ φ (x, z) ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)))
          = -∫ z in transverseBall m R, (F x • ψ.grad z) i * φ (x, z) := by
      intro x
      have hgC : ContDiff ℝ ∞ fun w : EuclideanSpace ℝ (Fin m) => φ (x, w) :=
        hφ.comp (contDiff_const.prodMk contDiff_id)
      have hgc : HasCompactSupport fun w : EuclideanSpace ℝ (Fin m) => φ (x, w) :=
        hasCompactSupport_sliceSnd hφc x
      have hgs : tsupport (fun w : EuclideanSpace ℝ (Fin m) => φ (x, w)) ⊆ transverseBall m R :=
        tsupport_sliceSnd_subset_ball hφs x
      have hw : (∫ z in transverseBall m R, ψ.toFun z *
            fderiv ℝ (fun w : EuclideanSpace ℝ (Fin m) => φ (x, w)) z
              (EuclideanSpace.single i 1))
          = -∫ z in transverseBall m R, ψ.grad z i * φ (x, z) :=
        ψ.hasWeakGrad (fun w : EuclideanSpace ℝ (Fin m) => φ (x, w)) hgC hgc hgs i
      have h1 : (∫ z in transverseBall m R, tensorFun F ψ (x, z) *
            fderiv ℝ φ (x, z) ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)))
          = F x * ∫ z in transverseBall m R, ψ.toFun z *
              fderiv ℝ (fun w : EuclideanSpace ℝ (Fin m) => φ (x, w)) z
                (EuclideanSpace.single i 1) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (.of_forall fun z => ?_)
        simp only [tensorFun_apply, fderiv_sliceSnd hφ1 x z]
        ring
      have h2 : (∫ z in transverseBall m R, (F x • ψ.grad z) i * φ (x, z))
          = F x * ∫ z in transverseBall m R, ψ.grad z i * φ (x, z) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (.of_forall fun z => ?_)
        simp only [PiLp.smul_apply, smul_eq_mul]
        ring
      rw [h1, h2, hw, mul_neg]
    calc (∫ p in bulkCyl a b m R, tensorFun F ψ p *
            fderiv ℝ φ p ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)))
        = ∫ x in Set.Ioo a b, ∫ z in transverseBall m R, tensorFun F ψ (x, z) *
            fderiv ℝ φ (x, z) ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)) := by
          rw [hmeas]; exact integral_prod _ hintL
      _ = ∫ x in Set.Ioo a b,
            -∫ z in transverseBall m R, (F x • ψ.grad z) i * φ (x, z) :=
          integral_congr_ae (.of_forall key)
      _ = -∫ x in Set.Ioo a b, ∫ z in transverseBall m R,
            (F x • ψ.grad z) i * φ (x, z) := integral_neg _
      _ = -∫ p in bulkCyl a b m R, (F p.1 • ψ.grad p.2) i * φ p := by
          rw [hmeas, integral_prod _ hintR]

/-! ### The element of `H1P Ω` -/

set_option linter.unusedVariables false in
/-- **The separated trial function as an element of `H¹(Ω)`.**  The hypothesis `hI : a < b` is
recorded because the cylinder is degenerate otherwise; it is not needed for the proofs, since
`Ioo a b` is bounded in any case. -/
def H1P.tensor (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) (hI : a < b) (ψ : TransH1 m R) :
    H1P (bulkCyl a b m R) where
  toFun := tensorFun F ψ
  gx := fun p => deriv F p.1 * ψ.toFun p.2
  gz := fun p => F p.1 • ψ.grad p.2
  memL2 := memLp_two_tensor hF.continuous ψ.memL2
  gx_memL2 := memLp_two_tensor (hF.continuous_deriv le_rfl) ψ.memL2
  gz_memL2 := memLp_two_tensor_vec hF.continuous ψ.grad_memL2
  hasWeakGrad := hasWeakGradP_tensor F hF ψ

@[simp] theorem H1P.tensor_toFun (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) (hI : a < b)
    (ψ : TransH1 m R) : (H1P.tensor F hF hI ψ).toFun = tensorFun F ψ := rfl

@[simp] theorem H1P.tensor_gx (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) (hI : a < b)
    (ψ : TransH1 m R) :
    (H1P.tensor F hF hI ψ).gx = fun p => deriv F p.1 * ψ.toFun p.2 := rfl

@[simp] theorem H1P.tensor_gz (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) (hI : a < b)
    (ψ : TransH1 m R) :
    (H1P.tensor F hF hI ψ).gz = fun p => F p.1 • ψ.grad p.2 := rfl

/-! ### Factorisation of the mass and of the Dirichlet energy -/

/-- **The mass factorises**: `N_Ω[F ⊗ ψ] = (∫_I F²) · N_B[ψ]`. -/
theorem massP_tensor (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) (hI : a < b) (ψ : TransH1 m R) :
    massP (H1P.tensor F hF hI ψ) = (∫ x in Set.Ioo a b, F x ^ 2) * NB ψ := by
  have h1 : massP (H1P.tensor F hF hI ψ)
      = ∫ p in bulkCyl a b m R, F p.1 ^ 2 * ψ.toFun p.2 ^ 2 := by
    refine integral_congr_ae (.of_forall fun p => ?_)
    show (F p.1 * ψ.toFun p.2) ^ 2 = _
    ring
  rw [h1, bulkCyl_eq]
  exact setIntegral_prod_mul (fun x => F x ^ 2) (fun z => ψ.toFun z ^ 2) _ _

/-- The two pieces of the Dirichlet integrand are separately integrable. -/
theorem integrable_tensor_dirichlet_axial (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F)
    (ψ : TransH1 m R) :
    Integrable (fun p : CapSpace m => deriv F p.1 ^ 2 * ψ.toFun p.2 ^ 2)
      (volume.restrict (bulkCyl a b m R)) := by
  rw [volume_restrict_bulkCyl]
  exact (integrable_sq_on_Ioo (a := a) (b := b)
    (hF.continuous_deriv le_rfl)).mul_prod ψ.memL2.integrable_sq

theorem integrable_tensor_dirichlet_transverse (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F)
    (ψ : TransH1 m R) :
    Integrable (fun p : CapSpace m => F p.1 ^ 2 * ‖ψ.grad p.2‖ ^ 2)
      (volume.restrict (bulkCyl a b m R)) := by
  rw [volume_restrict_bulkCyl]
  have hwn : Integrable (fun z => ‖ψ.grad z‖ ^ 2)
      (volume.restrict (transverseBall m R)) :=
    (memLp_two_iff_integrable_sq_norm ψ.grad_memL2.aestronglyMeasurable).1 ψ.grad_memL2
  exact (integrable_sq_on_Ioo (a := a) (b := b) hF.continuous).mul_prod hwn

/-- **The Dirichlet energy factorises**:
`D_Ω[F ⊗ ψ] = (∫_I F'²) · N_B[ψ] + (∫_I F²) · D_B[ψ]`. -/
theorem dirichletP_tensor (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) (hI : a < b) (ψ : TransH1 m R) :
    dirichletP (H1P.tensor F hF hI ψ)
      = (∫ x in Set.Ioo a b, deriv F x ^ 2) * NB ψ
        + (∫ x in Set.Ioo a b, F x ^ 2) * Weak.dirichlet ψ := by
  have hsplit : dirichletP (H1P.tensor F hF hI ψ)
      = (∫ p in bulkCyl a b m R, deriv F p.1 ^ 2 * ψ.toFun p.2 ^ 2)
        + ∫ p in bulkCyl a b m R, F p.1 ^ 2 * ‖ψ.grad p.2‖ ^ 2 := by
    rw [← integral_add (integrable_tensor_dirichlet_axial F hF ψ)
      (integrable_tensor_dirichlet_transverse F hF ψ)]
    refine integral_congr_ae (.of_forall fun p => ?_)
    have hn : ‖F p.1 • ψ.grad p.2‖ ^ 2 = F p.1 ^ 2 * ‖ψ.grad p.2‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    show (deriv F p.1 * ψ.toFun p.2) ^ 2 + ‖F p.1 • ψ.grad p.2‖ ^ 2
        = deriv F p.1 ^ 2 * ψ.toFun p.2 ^ 2 + F p.1 ^ 2 * ‖ψ.grad p.2‖ ^ 2
    rw [hn]
    ring
  have e1 : (∫ p in Set.Ioo a b ×ˢ transverseBall m R, deriv F p.1 ^ 2 * ψ.toFun p.2 ^ 2)
      = (∫ x in Set.Ioo a b, deriv F x ^ 2) * ∫ z in transverseBall m R, ψ.toFun z ^ 2 :=
    setIntegral_prod_mul (fun x => deriv F x ^ 2) (fun z => ψ.toFun z ^ 2) _ _
  have e2 : (∫ p in Set.Ioo a b ×ˢ transverseBall m R, F p.1 ^ 2 * ‖ψ.grad p.2‖ ^ 2)
      = (∫ x in Set.Ioo a b, F x ^ 2) * ∫ z in transverseBall m R, ‖ψ.grad z‖ ^ 2 :=
    setIntegral_prod_mul (fun x => F x ^ 2) (fun z => ‖ψ.grad z‖ ^ 2) _ _
  rw [hsplit, bulkCyl_eq, e1, e2]
  rfl

/-! ### The normalised case: `ψ = gs.psi` -/

variable {α : ℝ} {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}

/-- With the normalised transverse ground state, the mass of the trial function is exactly the
one-dimensional mass `∫_I F²`. -/
theorem massP_tensor_groundState (gs : TransverseGroundState m α R bd) (F : ℝ → ℝ)
    (hF : ContDiff ℝ 1 F) (hI : a < b) :
    massP (H1P.tensor F hF hI gs.psi) = ∫ x in Set.Ioo a b, F x ^ 2 := by
  rw [massP_tensor, gs.normalized, mul_one]

/-- With the normalised transverse ground state, the Dirichlet energy of the trial function is
`∫_I F'² + (∫_I F²) · D_B[ψ_R]`. -/
theorem dirichletP_tensor_groundState (gs : TransverseGroundState m α R bd) (F : ℝ → ℝ)
    (hF : ContDiff ℝ 1 F) (hI : a < b) :
    dirichletP (H1P.tensor F hF hI gs.psi)
      = (∫ x in Set.Ioo a b, deriv F x ^ 2)
        + (∫ x in Set.Ioo a b, F x ^ 2) * Weak.dirichlet gs.psi := by
  rw [dirichletP_tensor, gs.normalized, mul_one]

end

end RobinCaps.ThinDomain

