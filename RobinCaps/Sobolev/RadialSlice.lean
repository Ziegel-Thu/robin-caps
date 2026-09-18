import RobinCaps.ThinDomain.Slice
import RobinCaps.ThinDomain.Polar

/-!
# Radial (polar) slices of weak `H¹` functions on a ball

This file proves the *radial* ACL ("absolutely continuous on lines") property of weak `H¹`
functions on a Euclidean ball `B = ball 0 R ⊆ E = EuclideanSpace ℝ (Fin m)`, `m ≥ 1`: for almost
every direction `w` of the unit sphere the radial slice `r ↦ u (r • w)` is a one-dimensional
Sobolev function with weak derivative `r ↦ ⟪∇u (r • w), w⟫`.  It then builds the trace on the
sphere of radius `R` and proves the corresponding trace inequality.

This is the key step towards the trace inequality on the curved boundary of a hemispherical end
cap, and it is obtained without any general Lipschitz-domain trace theorem.

## Contents

* `HasWeakGrad.integral_inner_vectorField` (**deliverable 1**): the weak gradient tested
  against a smooth vector field `X`,
  `∫_D u ⟪∇Φ, X⟫ = - ∫_D ⟪g, X⟫ Φ - ∫_D u Φ (div X)`,
  obtained by applying the coordinate identities of `HasWeakGrad` to the test functions `Xᵢ Φ`.
* `ae_eq_zero_of_forall_contDiff_mul_eq_zero`: an `L¹` function on a closed subset `S ⊆ E`
  which is orthogonal to the restriction of every smooth function of `E` vanishes almost
  everywhere (smooth Urysohn plus dominated convergence).  This replaces the fundamental lemma
  of the calculus of variations on the sphere, which is not a vector space.
* `radialVec a k`, the globally smooth radial fields `x ↦ x / ‖x‖ ^ k` (cut off near the
  origin), with `divergence_radialVec`: `div (x/‖x‖^k) = (m - k)/‖x‖^k` for `‖x‖ ≥ a`; the
  choice `k = m` gives a *divergence-free* field, which is what makes the polar identity
  weightless.
* `integral_polar_symm`, `integral_ball_polar_symm`, `integral_volumeIoiPow`,
  `integrable_ball_angular`: polar coordinates with the *angular* integral outside (the
  companion of `RobinCaps.ThinDomain.integral_ball_polar`), together with the integrability of
  the angular function.
* `polarTest a φ χ x = φ ‖x‖ · χ (x/‖x‖)`, the polar test functions, and
  `integral_radialPairing_mul_eq_zero`: the polar identity
  `∫_S (∫_0^R (u(r w) φ'(r) + ⟪g(r w), w⟫ φ(r)) dr) χ(w) dσ(w) = 0`.
* `radialPairing_ae_eq_zero`: the radial pairing vanishes for almost every direction.
* `radialSlice_ae_of_hasWeakGrad` and `radialSlice_ae` (**deliverable 2**): the radial ACL
  property, `HasWeakDeriv ε R (u (· w)) (⟪g (· w), w⟫)` for every `ε ∈ (0,R)` and almost every
  `w`.  The passage from countably many test functions to all of them uses
  `RobinCaps.ThinDomain.hasWeakDeriv_of_idxBump`.
* `radialSlice_h1` (**deliverable 3**): the absolutely continuous representative of the radial
  slice in the concrete one-dimensional model `RobinCaps.Sobolev.H1 (R - ε)`, obtained after a
  translation (`hasWeakDeriv_translate`); `traceSphere`, the sphere trace, defined by an
  explicit choice-free formula, with `traceSphere_eq_of_continuous` (for a continuous
  representative the trace is the restriction to the sphere) and `traceSphere_eq_const_add`
  (the trace is the endpoint value of the FTC representative).
* `traceSphere_sq_le` and `traceSphere_sq_integral_le` (**deliverable 4**): the radial
  one-dimensional trace bound and the trace inequality
  `∫_S |Tr u|² dσ ≤ C(R,m) (‖u‖²_{L²(B)} + ‖∇u‖²_{L²(B)})`.

Everything is proved without `sorry`, `axiom` or `admit`.
-/
open MeasureTheory Metric Set Filter Module

open scoped ContDiff ENNReal Topology Manifold

namespace RobinCaps.Sobolev.Weak

set_option autoImplicit false

noncomputable section

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)

/-! ### Elementary coordinate identities on `EuclideanSpace` -/

/-- Expansion of a vector of `EuclideanSpace ℝ (Fin m)` in the standard basis. -/
theorem sum_smul_single (v : E) : ∑ i, v i • (EuclideanSpace.single i (1 : ℝ) : E) = v := by
  classical
  have h := (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr v
  simpa [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using h

/-- The value of a continuous linear form on a vector, expanded in coordinates. -/
theorem clm_apply_eq_sum (L : E →L[ℝ] ℝ) (v : E) :
    L v = ∑ i, v i * L (EuclideanSpace.single i 1) := by
  conv_lhs => rw [← sum_smul_single v]
  rw [map_sum]
  simp [smul_eq_mul]

/-- The Euclidean inner product in coordinates. -/
theorem inner_eq_sum (a b : E) : inner ℝ a b = ∑ i, a i * b i := by
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun i _ => by simp [mul_comm]

/-! ### Deliverable 1: the weak gradient tested against a smooth vector field -/

namespace HasWeakGrad

variable {D : Set (EuclideanSpace ℝ (Fin m))} {u : EuclideanSpace ℝ (Fin m) → ℝ}
  {g : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}

/-- The `i`-th component of a smooth vector field is smooth. -/
theorem contDiff_comp_proj {X : E → E} (hX : ContDiff ℝ ∞ X) (i : Fin m) :
    ContDiff ℝ ∞ fun x => X x i :=
  ((EuclideanSpace.proj i : E →L[ℝ] ℝ).contDiff).comp hX

/-- The partial derivative of the `i`-th component of a smooth vector field. -/
theorem fderiv_comp_proj {X : E → E} (hX : ContDiff ℝ ∞ X) (i j : Fin m) (x : E) :
    fderiv ℝ (fun y => X y i) x (EuclideanSpace.single j 1)
      = fderiv ℝ X x (EuclideanSpace.single j 1) i := by
  have hd : HasFDerivAt (fun y => X y i)
      ((EuclideanSpace.proj i : E →L[ℝ] ℝ).comp (fderiv ℝ X x)) x :=
    (EuclideanSpace.proj i : E →L[ℝ] ℝ).hasFDerivAt.comp x
      ((hX.differentiable (by simp)).differentiableAt.hasFDerivAt)
  rw [hd.fderiv]
  rfl

/-- The topological support of a product is contained in that of the right factor. -/
theorem tsupport_mul_right (f : E → ℝ) (Φ : E → ℝ) :
    tsupport (fun x => f x * Φ x) ⊆ tsupport Φ :=
  closure_mono (Function.support_mul_subset_right f Φ)

/-- **The weak gradient tested against a smooth vector field.**  For a test function `Φ`
(smooth, compactly supported in `D`) and a globally smooth vector field `X`,

`∫_D u ⟪∇Φ, X⟫ = - ∫_D ⟪g, X⟫ Φ - ∫_D u Φ (div X)`.

This is the multi-dimensional integration-by-parts formula in the weak setting; it is proved by
applying the defining coordinate identities of `HasWeakGrad` to the test functions `Xᵢ Φ` and
summing over `i`, using `∂ᵢ(Xᵢ Φ) = Xᵢ ∂ᵢΦ + Φ ∂ᵢXᵢ`. -/
theorem integral_inner_vectorField
    (hu : MemLp u 2 (volume.restrict D)) (hg : MemLp g 2 (volume.restrict D))
    (hw : HasWeakGrad D u g) {Φ : E → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hΦc : HasCompactSupport Φ)
    (hΦs : tsupport Φ ⊆ D) {X : E → E} (hX : ContDiff ℝ ∞ X) :
    ∫ x in D, u x * fderiv ℝ Φ x (X x)
      = -(∫ x in D, inner ℝ (g x) (X x) * Φ x)
        - ∫ x in D, u x * Φ x * ∑ i, fderiv ℝ X x (EuclideanSpace.single i 1) i := by
  classical
  -- the test functions `Xᵢ Φ`
  have hXi : ∀ i : Fin m, ContDiff ℝ ∞ fun x => X x i := fun i => contDiff_comp_proj hX i
  have htest : ∀ i : Fin m, ContDiff ℝ ∞ fun x => X x i * Φ x := fun i => (hXi i).mul hΦ
  have htestc : ∀ i : Fin m, HasCompactSupport fun x => X x i * Φ x := fun _ => hΦc.mul_left
  have htests : ∀ i : Fin m, tsupport (fun x => X x i * Φ x) ⊆ D := fun i =>
    (tsupport_mul_right _ _).trans hΦs
  -- continuity of the various factors
  have hcΦ : ∀ i : Fin m, Continuous fun x => fderiv ℝ Φ x (EuclideanSpace.single i 1) :=
    fun i => (hΦ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcX : ∀ i : Fin m, Continuous fun x => fderiv ℝ X x (EuclideanSpace.single i 1) i := by
    intro i
    exact (EuclideanSpace.proj i : E →L[ℝ] ℝ).continuous.comp
      ((hX.continuous_fderiv (by simp)).clm_apply continuous_const)
  -- the three families of integrands
  have hFint : ∀ i : Fin m, Integrable
      (fun x : E => u x * (X x i * fderiv ℝ Φ x (EuclideanSpace.single i 1)))
      (volume.restrict D) := by
    intro i
    have h3 : MemLp (fun x : E => X x i * fderiv ℝ Φ x (EuclideanSpace.single i 1)) 2
        (volume.restrict D) :=
      ((hXi i).continuous.mul (hcΦ i)).memLp_of_hasCompactSupport
        ((hΦc.fderiv_apply ℝ (EuclideanSpace.single i 1)).mul_left)
    exact hu.integrable_mul h3
  have hGint : ∀ i : Fin m, Integrable
      (fun x : E => u x * (Φ x * fderiv ℝ X x (EuclideanSpace.single i 1) i))
      (volume.restrict D) := by
    intro i
    have h3 : MemLp (fun x : E => Φ x * fderiv ℝ X x (EuclideanSpace.single i 1) i) 2
        (volume.restrict D) :=
      (hΦ.continuous.mul (hcX i)).memLp_of_hasCompactSupport hΦc.mul_right
    exact hu.integrable_mul h3
  have hHint : ∀ i : Fin m, Integrable (fun x : E => g x i * (X x i * Φ x))
      (volume.restrict D) := by
    intro i
    exact (memLp_two_comp hg i).integrable_mul (memLp_two_of_test (htest i) (htestc i))
  -- the coordinate identity for the test function `Xᵢ Φ`
  have key : ∀ i : Fin m,
      (∫ x in D, u x * (X x i * fderiv ℝ Φ x (EuclideanSpace.single i 1)))
        + ∫ x in D, u x * (Φ x * fderiv ℝ X x (EuclideanSpace.single i 1) i)
        = - ∫ x in D, g x i * (X x i * Φ x) := by
    intro i
    have h := hw (fun x => X x i * Φ x) (htest i) (htestc i) (htests i) i
    have hder : ∀ x : E, fderiv ℝ (fun y => X y i * Φ y) x (EuclideanSpace.single i 1)
        = X x i * fderiv ℝ Φ x (EuclideanSpace.single i 1)
          + Φ x * fderiv ℝ X x (EuclideanSpace.single i 1) i := by
      intro x
      have hd : HasFDerivAt (fun y : E => X y i * Φ y)
          (X x i • fderiv ℝ Φ x + Φ x • fderiv ℝ (fun y : E => X y i) x) x :=
        (((hXi i).differentiable (by simp)) x).hasFDerivAt.mul
          (((hΦ.differentiable (by simp)) x).hasFDerivAt)
      rw [hd.fderiv]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [fderiv_comp_proj hX i i x]
    have hlhs : (∫ x in D, u x * (X x i * fderiv ℝ Φ x (EuclideanSpace.single i 1)))
        + ∫ x in D, u x * (Φ x * fderiv ℝ X x (EuclideanSpace.single i 1) i)
        = ∫ x in D, u x * fderiv ℝ (fun y => X y i * Φ y) x (EuclideanSpace.single i 1) := by
      rw [← integral_add (hFint i) (hGint i)]
      refine integral_congr_ae (.of_forall fun x => ?_)
      dsimp only
      rw [hder x]
      ring
    rw [hlhs, h]
  -- summing over the coordinates
  have hsum : (∑ i, ∫ x in D, u x * (X x i * fderiv ℝ Φ x (EuclideanSpace.single i 1)))
      + ∑ i, ∫ x in D, u x * (Φ x * fderiv ℝ X x (EuclideanSpace.single i 1) i)
      = - ∑ i, ∫ x in D, g x i * (X x i * Φ x) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => key i
  have e1 : ∫ x in D, u x * fderiv ℝ Φ x (X x)
      = ∑ i, ∫ x in D, u x * (X x i * fderiv ℝ Φ x (EuclideanSpace.single i 1)) := by
    rw [← integral_finset_sum _ fun i _ => hFint i]
    refine integral_congr_ae (.of_forall fun x => ?_)
    dsimp only
    rw [clm_apply_eq_sum (fderiv ℝ Φ x) (X x), Finset.mul_sum]
  have e2 : (∫ x in D, u x * Φ x * ∑ i, fderiv ℝ X x (EuclideanSpace.single i 1) i)
      = ∑ i, ∫ x in D, u x * (Φ x * fderiv ℝ X x (EuclideanSpace.single i 1) i) := by
    rw [← integral_finset_sum _ fun i _ => hGint i]
    refine integral_congr_ae (.of_forall fun x => ?_)
    dsimp only
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e3 : (∫ x in D, inner ℝ (g x) (X x) * Φ x)
      = ∑ i, ∫ x in D, g x i * (X x i * Φ x) := by
    rw [← integral_finset_sum _ fun i _ => hHint i]
    refine integral_congr_ae (.of_forall fun x => ?_)
    dsimp only
    rw [inner_eq_sum (g x) (X x), Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2, e3]
  linarith [hsum]

end HasWeakGrad

/-! ### An `L¹` function orthogonal to all smooth functions vanishes

The exceptional set of the polar identity has to be removed by a duality argument on the unit
sphere.  Since mathlib's fundamental lemma of the calculus of variations is stated on a
finite-dimensional vector space (or manifold), and the test functions available on the sphere
are the restrictions of the smooth functions of the ambient space, we prove directly that an
integrable function on a closed subset `S ⊆ E` which is orthogonal to every smooth function of
`E` vanishes almost everywhere.  The proof approximates the indicator of a closed subset of `S`
by smooth functions of `E` (smooth Urysohn lemma) and uses dominated convergence. -/

/-- **Smooth Urysohn.**  For a closed set `T ⊆ E` and `ε > 0` there is a smooth function equal
to `1` on `T`, vanishing outside the `ε`-thickening of `T`, with values in `[0,1]`. -/
theorem exists_contDiff_one_on_isClosed {T : Set (EuclideanSpace ℝ (Fin m))} (hT : IsClosed T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : EuclideanSpace ℝ (Fin m) → ℝ, ContDiff ℝ ∞ f ∧ (∀ x ∈ T, f x = 1) ∧
      (∀ x, x ∉ thickening ε T → f x = 0) ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
  have h1 : IsClosed (thickening ε T)ᶜ := isOpen_thickening.isClosed_compl
  have hd : Disjoint ((thickening ε T)ᶜ) T := by
    refine Set.disjoint_left.2 fun x hx hxT => hx ?_
    exact self_subset_thickening hε T hxT
  obtain ⟨f, hf0, hf1, hfI⟩ :=
    exists_smooth_zero_one_of_isClosed (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) h1 hT hd
  refine ⟨f, ?_, fun x hx => ?_, fun x hx => ?_, hfI⟩
  · rw [← contMDiff_iff_contDiff]
    exact f.contMDiff
  · simpa using hf1 hx
  · simpa using hf0 hx

/-- **Duality with smooth functions.**  An integrable function on (a measure space structure
carried by) a closed subset `S` of `E` whose integral against the restriction of every smooth
function of `E` vanishes is almost everywhere zero. -/
theorem ae_eq_zero_of_forall_contDiff_mul_eq_zero {S : Set (EuclideanSpace ℝ (Fin m))}
    (hS : IsClosed S) {σ : Measure S} {A : S → ℝ} (hA : Integrable A σ)
    (h : ∀ χ : EuclideanSpace ℝ (Fin m) → ℝ, ContDiff ℝ ∞ χ →
      ∫ w, A w * χ (w : EuclideanSpace ℝ (Fin m)) ∂σ = 0) :
    A =ᵐ[σ] 0 := by
  refine ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero hA fun F hF => ?_
  have hTclosed : IsClosed (Subtype.val '' F) :=
    (hS.isClosedEmbedding_subtypeVal).isClosedMap F hF
  choose χ hχs hχone hχzero hχmem using fun n : ℕ =>
    exists_contDiff_one_on_isClosed hTclosed (ε := 1 / (n + 1))
      (by positivity : (0:ℝ) < 1 / (n + 1))
  have hbound : ∀ n : ℕ, ∀ w : S, ‖A w * χ n (w : EuclideanSpace ℝ (Fin m))‖ ≤ ‖A w‖ := by
    intro n w
    rw [norm_mul]
    have h1 : ‖χ n (w : EuclideanSpace ℝ (Fin m))‖ ≤ 1 := by
      obtain ⟨h0, h1⟩ := hχmem n (w : EuclideanSpace ℝ (Fin m))
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact h1
    nlinarith [norm_nonneg (A w), norm_nonneg (χ n (w : EuclideanSpace ℝ (Fin m)))]
  have hmeas : ∀ n : ℕ,
      AEStronglyMeasurable (fun w : S => A w * χ n (w : EuclideanSpace ℝ (Fin m))) σ := by
    intro n
    exact hA.aestronglyMeasurable.mul
      (((hχs n).continuous.comp continuous_subtype_val).aestronglyMeasurable)
  have hlim : ∀ w : S, Tendsto (fun n : ℕ => A w * χ n (w : EuclideanSpace ℝ (Fin m)))
      atTop (𝓝 (F.indicator A w)) := by
    intro w
    by_cases hw : w ∈ F
    · have hcst : ∀ n : ℕ, A w * χ n (w : EuclideanSpace ℝ (Fin m)) = F.indicator A w := by
        intro n
        rw [hχone n _ (Set.mem_image_of_mem _ hw), mul_one, Set.indicator_of_mem hw]
      simp only [hcst]
      exact tendsto_const_nhds
    · have hnot : (w : EuclideanSpace ℝ (Fin m)) ∉ (Subtype.val '' F) := by
        rintro ⟨y, hy, hxy⟩
        exact hw (by rwa [Subtype.val_injective hxy] at hy)
      obtain ⟨δ, hδ, hδ'⟩ : ∃ δ, 0 < δ ∧
          (w : EuclideanSpace ℝ (Fin m)) ∉ thickening δ (Subtype.val '' F) := by
        rw [← hTclosed.closure_eq, closure_eq_iInter_thickening] at hnot
        simpa using hnot
      have hev : ∀ᶠ n : ℕ in atTop, A w * χ n (w : EuclideanSpace ℝ (Fin m)) = 0 := by
        have htend : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        filter_upwards [(tendsto_order.1 htend).2 δ hδ] with n hn
        have hz : χ n (w : EuclideanSpace ℝ (Fin m)) = 0 := by
          refine hχzero n _ fun hmem => hδ' ?_
          exact thickening_mono hn.le _ hmem
        rw [hz, mul_zero]
      rw [Set.indicator_of_notMem hw]
      exact Tendsto.congr' (hev.mono fun n hn => hn.symm) tendsto_const_nhds
  have hconv := tendsto_integral_of_dominated_convergence (fun w : S => ‖A w‖) hmeas hA.norm
    (fun n => Eventually.of_forall (hbound n)) (Eventually.of_forall hlim)
  have hzero : ∀ n : ℕ, ∫ w, A w * χ n (w : EuclideanSpace ℝ (Fin m)) ∂σ = 0 :=
    fun n => h _ (hχs n)
  simp only [hzero] at hconv
  have hlast := tendsto_nhds_unique hconv tendsto_const_nhds
  rwa [integral_indicator hF.measurableSet] at hlast



/-! ### Smooth radial fields

Polar test functions are built from two radial vector fields which are *globally* smooth on `E`
and agree, outside a ball of radius `a`, with `x / ‖x‖` (the radial projection onto the unit
sphere, used to build the angular part of the test function) and with `x / ‖x‖ ^ m` (the
divergence-free radial field, used as the vector field `X` of
`HasWeakGrad.integral_inner_vectorField`).  Both are of the form `c (‖x‖ ^ 2) • x`, and
smoothness at the origin is obtained by cutting `c` off near `0`. -/

/-- A smooth cut-off in the *squared* radius: `cutOff a s = 0` for `s ≤ a² / 4` and `= 1` for
`s ≥ a² / 2`. -/
def cutOff (a s : ℝ) : ℝ := Real.smoothTransition ((s - a ^ 2 / 4) / (a ^ 2 / 4))

theorem cutOff_contDiff (a : ℝ) : ContDiff ℝ ∞ (cutOff a) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

theorem cutOff_eq_zero {a s : ℝ} (ha : 0 < a) (hs : s ≤ a ^ 2 / 4) : cutOff a s = 0 := by
  have h4 : (0 : ℝ) < a ^ 2 / 4 := by positivity
  exact Real.smoothTransition.zero_of_nonpos (div_nonpos_iff.2 (Or.inr ⟨by linarith, h4.le⟩))

theorem cutOff_eq_one {a s : ℝ} (ha : 0 < a) (hs : a ^ 2 / 2 ≤ s) : cutOff a s = 1 := by
  have h4 : (0 : ℝ) < a ^ 2 / 4 := by positivity
  refine Real.smoothTransition.one_of_one_le ?_
  rw [le_div_iff₀ h4]
  linarith

/-- The radial coefficient: `radialCoef a k s` agrees with `(√s)⁻ᵏ` for `s ≥ a² / 2` and is
smooth on all of `ℝ`. -/
def radialCoef (a : ℝ) (k : ℕ) (s : ℝ) : ℝ := cutOff a s * ((Real.sqrt s) ^ k)⁻¹

theorem radialCoef_of_le {a : ℝ} (ha : 0 < a) (k : ℕ) {s : ℝ} (hs : a ^ 2 / 2 ≤ s) :
    radialCoef a k s = ((Real.sqrt s) ^ k)⁻¹ := by
  rw [radialCoef, cutOff_eq_one ha hs, one_mul]

theorem radialCoef_contDiff {a : ℝ} (ha : 0 < a) (k : ℕ) : ContDiff ℝ ∞ (radialCoef a k) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  rcases lt_or_ge 0 s with hs | hs
  · have h1 : ContDiffAt ℝ ∞ Real.sqrt s := Real.contDiffAt_sqrt hs.ne'
    have h2 : (Real.sqrt s) ^ k ≠ 0 := pow_ne_zero _ (Real.sqrt_pos.2 hs).ne'
    exact ((cutOff_contDiff a).contDiffAt).mul ((h1.pow k).inv h2)
  · have hz : ∀ᶠ t in 𝓝 s, radialCoef a k t = 0 := by
      have hopen : Iio (a ^ 2 / 4) ∈ 𝓝 s := by
        refine Iio_mem_nhds ?_
        have : (0 : ℝ) < a ^ 2 / 4 := by positivity
        linarith
      filter_upwards [hopen] with t ht
      rw [radialCoef, cutOff_eq_zero ha (le_of_lt ht), zero_mul]
    exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const hz

/-- The derivative of the radial coefficient where it is a genuine power. -/
theorem radialCoef_hasDerivAt {a : ℝ} (ha : 0 < a) (k : ℕ) {s : ℝ} (hs : a ^ 2 / 2 < s) :
    HasDerivAt (radialCoef a k) (-((k : ℝ) / 2) * ((Real.sqrt s) ^ (k + 2))⁻¹) s := by
  have hspos : 0 < s := lt_of_le_of_lt (by positivity) hs
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hspos
  have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt s)) s := Real.hasDerivAt_sqrt hspos.ne'
  have hinv : HasDerivAt (fun t => ((Real.sqrt t) ^ k)⁻¹)
      (-((k : ℝ) * (Real.sqrt s) ^ (k - 1) * (1 / (2 * Real.sqrt s))) / ((Real.sqrt s) ^ k) ^ 2)
      s := (hsqrt.pow k).inv (pow_ne_zero _ hsq.ne')
  have heq : radialCoef a k =ᶠ[𝓝 s] fun t => ((Real.sqrt t) ^ k)⁻¹ := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    exact radialCoef_of_le ha k (le_of_lt ht)
  have hmain := hinv.congr_of_eventuallyEq heq
  convert hmain using 1
  have hsne : Real.sqrt s ≠ 0 := hsq.ne'
  match k with
  | 0 => simp
  | (j + 1) =>
    have hj : (j + 1) - 1 = j := rfl
    rw [hj]
    field_simp
    ring


/-- The radial vector field `radialVec a k x = c_k (‖x‖²) • x`, which agrees with
`x / ‖x‖ ^ k` outside the ball of radius `a` and is smooth on all of `E`. -/
def radialVec (a : ℝ) (k : ℕ) (x : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin m) :=
  radialCoef a k (‖x‖ ^ 2) • x

theorem radialVec_contDiff {a : ℝ} (ha : 0 < a) (k : ℕ) :
    ContDiff ℝ ∞ (radialVec (m := m) a k) :=
  ((radialCoef_contDiff ha k).comp (contDiff_norm_sq ℝ)).smul contDiff_id

/-- On the sphere of radius `t ≥ a`, the field is `t ^ (1 - k)` times the direction. -/
theorem radialVec_smul {a : ℝ} (ha : 0 < a) (k : ℕ) {t : ℝ} (ht : a ≤ t)
    (w : EuclideanSpace ℝ (Fin m)) (hw : ‖w‖ = 1) :
    radialVec a k (t • w) = ((t ^ k)⁻¹ * t) • w := by
  have ht0 : 0 < t := lt_of_lt_of_le ha ht
  have hnorm : ‖t • w‖ = t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0, hw, mul_one]
  have hs : a ^ 2 / 2 ≤ ‖t • w‖ ^ 2 := by
    rw [hnorm]
    nlinarith
  rw [radialVec, radialCoef_of_le ha k hs, hnorm, Real.sqrt_sq ht0.le, smul_smul]

theorem radialVec_norm_lt {a : ℝ} (ha : 0 < a) (k : ℕ) {x : EuclideanSpace ℝ (Fin m)}
    (hx : ‖x‖ ^ 2 ≤ a ^ 2 / 4) : radialVec a k x = 0 := by
  rw [radialVec, radialCoef, cutOff_eq_zero ha hx, zero_mul, zero_smul]

/-- **The divergence of the radial field.**  For `‖x‖ ≥ a` one has
`div (x / ‖x‖ ^ k) = (m - k) / ‖x‖ ^ k`; in particular the field `radialVec a m` is divergence
free there. -/
theorem divergence_radialVec {a : ℝ} (ha : 0 < a) (k : ℕ) {x : EuclideanSpace ℝ (Fin m)}
    (hx : a ≤ ‖x‖) :
    ∑ i, fderiv ℝ (radialVec a k) x (EuclideanSpace.single i 1) i
      = ((m : ℝ) - k) * (‖x‖ ^ k)⁻¹ := by
  have hxpos : 0 < ‖x‖ := lt_of_lt_of_le ha hx
  have hs : a ^ 2 / 2 < ‖x‖ ^ 2 := by nlinarith
  have hsqrt : Real.sqrt (‖x‖ ^ 2) = ‖x‖ := Real.sqrt_sq (norm_nonneg x)
  set cval : ℝ := -((k : ℝ) / 2) * ((Real.sqrt (‖x‖ ^ 2)) ^ (k + 2))⁻¹ with hcval
  have hc : HasDerivAt (radialCoef a k) cval (‖x‖ ^ 2) := radialCoef_hasDerivAt ha k hs
  have hN : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin m) => ‖y‖ ^ 2) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hc'' : HasFDerivAt ((radialCoef a k) ∘ (fun y : EuclideanSpace ℝ (Fin m) => ‖y‖ ^ 2))
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) cval).comp (2 • innerSL ℝ x)) x :=
    (hc.hasFDerivAt).comp x hN
  have hc' : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin m) => radialCoef a k (‖y‖ ^ 2))
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) cval).comp (2 • innerSL ℝ x)) x := hc''
  have hd : HasFDerivAt (radialVec a k)
      (radialCoef a k (‖x‖ ^ 2) • (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin m)))
        + ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) cval).comp
            (2 • innerSL ℝ x)).smulRight x) x := by
    exact hc'.fun_smul (hasFDerivAt_id x)
  have hfd : ∀ i : Fin m, fderiv ℝ (radialVec a k) x (EuclideanSpace.single i 1) i
      = radialCoef a k (‖x‖ ^ 2) + 2 * cval * (x i) ^ 2 := by
    intro i
    rw [hd.fderiv]
    simp [EuclideanSpace.single_apply, EuclideanSpace.inner_single_right, mul_comm]
    ring
  rw [Finset.sum_congr rfl fun i _ => hfd i, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnormsq : ∑ i, (x i) ^ 2 = ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_eq_sum]
    exact Finset.sum_congr rfl fun i _ => pow_two (x i)
  rw [← Finset.mul_sum, hnormsq, radialCoef_of_le ha k hs.le, hcval, hsqrt]
  have hne : ‖x‖ ≠ 0 := hxpos.ne'
  field_simp
  ring


/-! ### Polar coordinates with the angular integral outside

`RobinCaps.ThinDomain.integral_ball_polar` reduces an integral over a ball to
`∫_r r^{m-1} ∫_w`.  For the radial slicing we need the two integrals in the *other* order,
together with the integrability of the angular function `w ↦ ∫_r ...`; both come from Fubini
for the product measure `σ ⊗ volumeIoiPow (m-1)` transported by the polar homeomorphism, as in
`RobinCaps.ThinDomain.integral_polar`. -/

open RobinCaps.ThinDomain in
/-- The measure `volumeIoiPow k` on the subtype `Ioi 0` integrates as the weight `r ^ k`. -/
theorem integral_volumeIoiPow (k : ℕ) (G : ℝ → ℝ) :
    ∫ r : Ioi (0 : ℝ), G (r : ℝ) ∂(Measure.volumeIoiPow k)
      = ∫ r in Ioi (0 : ℝ), r ^ k * G r := by
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul,
    integral_subtype_comap measurableSet_Ioi (fun a : ℝ => Real.toNNReal (a ^ k) • G a)]
  · refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hx.out.le _), smul_eq_mul]
  · exact (measurable_subtype_coe.pow_const _).real_toNNReal

open RobinCaps.ThinDomain in
/-- **Polar coordinates with the angular integral outside.** -/
theorem integral_polar_symm (hm : 1 ≤ m) (F : EuclideanSpace ℝ (Fin m) → ℝ)
    (hF : Integrable F) :
    ∫ z, F z = ∫ w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      (∫ r in Ioi (0 : ℝ), r ^ (m - 1) * F (r • (w : EuclideanSpace ℝ (Fin m))))
        ∂(sphereMeasure m) := by
  haveI := nontrivial_euclidean hm
  set μ : Measure (EuclideanSpace ℝ (Fin m)) := volume with hμ
  have hrank : finrank ℝ (EuclideanSpace ℝ (Fin m)) - 1 = m - 1 := by rw [finrank_eq]
  have key : ∫ z, F z ∂μ = ∫ w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      (∫ r : Ioi (0 : ℝ), F ((r : ℝ) • (w : EuclideanSpace ℝ (Fin m)))
        ∂(Measure.volumeIoiPow (finrank ℝ (EuclideanSpace ℝ (Fin m)) - 1))) ∂μ.toSphere := by
    calc ∫ z, F z ∂μ
        = ∫ x : (({0} : Set (EuclideanSpace ℝ (Fin m)))ᶜ : Set (EuclideanSpace ℝ (Fin m))),
            F (x : EuclideanSpace ℝ (Fin m)) ∂(Measure.comap (↑) μ) := by
          rw [integral_subtype_comap (measurableSet_singleton
            (0 : EuclideanSpace ℝ (Fin m))).compl F, restrict_compl_singleton]
      _ = ∫ p, F ((p.2 : ℝ) • (p.1 : EuclideanSpace ℝ (Fin m)))
            ∂(μ.toSphere.prod
              (Measure.volumeIoiPow (finrank ℝ (EuclideanSpace ℝ (Fin m)) - 1))) := by
          rw [← μ.measurePreserving_homeomorphUnitSphereProd.integral_comp
            (Homeomorph.measurableEmbedding _)
            (fun p : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 × Ioi (0 : ℝ) =>
              F ((p.2 : ℝ) • (p.1 : EuclideanSpace ℝ (Fin m))))]
          exact integral_congr_ae (Eventually.of_forall fun x => (polar_comp_apply F x).symm)
      _ = _ := integral_prod _ ((integrable_polar_iff μ F).2 hF)
  rw [key]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  rw [hrank]
  exact integral_volumeIoiPow (m - 1) (fun r => F (r • (w : EuclideanSpace ℝ (Fin m))))

open RobinCaps.ThinDomain in
/-- The angular function `w ↦ ∫_r r^{m-1} F (r w)` is integrable on the sphere. -/
theorem integrable_angular (hm : 1 ≤ m) (F : EuclideanSpace ℝ (Fin m) → ℝ)
    (hF : Integrable F) :
    Integrable (fun w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      ∫ r in Ioi (0 : ℝ), r ^ (m - 1) * F (r • (w : EuclideanSpace ℝ (Fin m))))
      (sphereMeasure m) := by
  haveI := nontrivial_euclidean hm
  set μ : Measure (EuclideanSpace ℝ (Fin m)) := volume with hμ
  have hrank : finrank ℝ (EuclideanSpace ℝ (Fin m)) - 1 = m - 1 := by rw [finrank_eq]
  have hint := ((integrable_polar_iff μ F).2 hF).integral_prod_left
  rw [hrank] at hint
  refine hint.congr (Eventually.of_forall fun w => ?_)
  exact integral_volumeIoiPow (m - 1) (fun r => F (r • (w : EuclideanSpace ℝ (Fin m))))


open RobinCaps.ThinDomain in
/-- The polar decomposition of the indicator of a ball: for `w` on the unit sphere and `r > 0`,
`r ^ (m-1) * (ball 0 R).indicator f (r w)` is the indicator of `Ioo 0 R` of
`r ^ (m-1) * f (r w)`. -/
theorem indicator_polar_eq {R : ℝ} (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
    EqOn (fun r : ℝ => r ^ (m - 1) *
        (ball (0 : EuclideanSpace ℝ (Fin m)) R).indicator f (r • (w : EuclideanSpace ℝ (Fin m))))
      ((Ioo (0 : ℝ) R).indicator
        (fun r : ℝ => r ^ (m - 1) * f (r • (w : EuclideanSpace ℝ (Fin m))))) (Ioi (0 : ℝ)) := by
  intro r hr
  have hr0 : (0 : ℝ) < r := hr
  dsimp only
  by_cases hrR : r < R
  · rw [Set.indicator_of_mem (by simpa [mem_ball_zero_iff, norm_smul_sphere hr0 w] using hrR) f,
      Set.indicator_of_mem (Set.mem_Ioo.2 ⟨hr0, hrR⟩)]
  · rw [Set.indicator_of_notMem (by simpa [mem_ball_zero_iff, norm_smul_sphere hr0 w] using hrR) f,
      Set.indicator_of_notMem (fun h => hrR h.2), mul_zero]

open RobinCaps.ThinDomain in
/-- **Polar coordinates over a ball with the angular integral outside.** -/
theorem integral_ball_polar_symm (hm : 1 ≤ m) {R : ℝ} {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf : IntegrableOn f (ball (0 : EuclideanSpace ℝ (Fin m)) R)) :
    ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) R, f z
      = ∫ w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        (∫ r in Ioo (0 : ℝ) R, r ^ (m - 1) * f (r • (w : EuclideanSpace ℝ (Fin m))))
          ∂(sphereMeasure m) := by
  have hF : Integrable ((ball (0 : EuclideanSpace ℝ (Fin m)) R).indicator f) :=
    hf.integrable_indicator measurableSet_ball
  rw [← integral_indicator measurableSet_ball, integral_polar_symm hm _ hF]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  dsimp only
  rw [setIntegral_congr_fun measurableSet_Ioi (indicator_polar_eq f w),
    setIntegral_indicator measurableSet_Ioo,
    Set.inter_eq_self_of_subset_right Set.Ioo_subset_Ioi_self]

open RobinCaps.ThinDomain in
/-- The angular function of a ball integral is integrable on the sphere. -/
theorem integrable_ball_angular (hm : 1 ≤ m) {R : ℝ} {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf : IntegrableOn f (ball (0 : EuclideanSpace ℝ (Fin m)) R)) :
    Integrable (fun w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      ∫ r in Ioo (0 : ℝ) R, r ^ (m - 1) * f (r • (w : EuclideanSpace ℝ (Fin m))))
      (sphereMeasure m) := by
  have hF : Integrable ((ball (0 : EuclideanSpace ℝ (Fin m)) R).indicator f) :=
    hf.integrable_indicator measurableSet_ball
  refine (integrable_angular hm _ hF).congr (Eventually.of_forall fun w => ?_)
  dsimp only
  rw [setIntegral_congr_fun measurableSet_Ioi (indicator_polar_eq f w),
    setIntegral_indicator measurableSet_Ioo,
    Set.inter_eq_self_of_subset_right Set.Ioo_subset_Ioi_self]


/-! ### Integrability of the two pairings -/

/-- `u ∈ L²` against the derivative of a test function in a smooth direction field. -/
theorem integrable_mul_fderiv_vectorField {D : Set (EuclideanSpace ℝ (Fin m))}
    {u : EuclideanSpace ℝ (Fin m) → ℝ} (hu : MemLp u 2 (volume.restrict D))
    {Φ : EuclideanSpace ℝ (Fin m) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hΦc : HasCompactSupport Φ)
    {X : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)} (hX : ContDiff ℝ ∞ X) :
    Integrable (fun x => u x * fderiv ℝ Φ x (X x)) (volume.restrict D) := by
  have hcont : Continuous fun x : EuclideanSpace ℝ (Fin m) => fderiv ℝ Φ x (X x) :=
    (hΦ.continuous_fderiv (by simp)).clm_apply hX.continuous
  have hsupp : HasCompactSupport fun x : EuclideanSpace ℝ (Fin m) => fderiv ℝ Φ x (X x) := by
    refine HasCompactSupport.intro hΦc ?_
    intro x hx
    have : fderiv ℝ Φ x = 0 :=
      Function.notMem_support.1 fun h => hx (support_fderiv_subset ℝ h)
    rw [this]
    rfl
  have hL2 : MemLp (fun x : EuclideanSpace ℝ (Fin m) => fderiv ℝ Φ x (X x)) 2
      (volume.restrict D) := hcont.memLp_of_hasCompactSupport hsupp
  exact hu.integrable_mul hL2

/-- `g ∈ L²` paired with a smooth direction field against a test function. -/
theorem integrable_inner_mul_test {D : Set (EuclideanSpace ℝ (Fin m))}
    {g : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    (hg : MemLp g 2 (volume.restrict D))
    {Φ : EuclideanSpace ℝ (Fin m) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hΦc : HasCompactSupport Φ)
    {X : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)} (hX : ContDiff ℝ ∞ X) :
    Integrable (fun x => inner ℝ (g x) (X x) * Φ x) (volume.restrict D) := by
  have hi : ∀ i : Fin m, Integrable (fun x : EuclideanSpace ℝ (Fin m) => g x i * (X x i * Φ x))
      (volume.restrict D) := by
    intro i
    exact (memLp_two_comp hg i).integrable_mul
      (memLp_two_of_test ((HasWeakGrad.contDiff_comp_proj hX i).mul hΦ) hΦc.mul_left)
  refine (integrable_finset_sum (μ := volume.restrict D) Finset.univ
    fun i _ => hi i).congr (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [inner_eq_sum (g x) (X x), Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ### Polar test functions -/

/-- The polar test function `Φ (x) = φ ‖x‖ · χ (x / ‖x‖)`, built with the smooth radial
projection `radialVec a 1`. -/
def polarTest (a : ℝ) (φ : ℝ → ℝ) (χ : EuclideanSpace ℝ (Fin m) → ℝ)
    (x : EuclideanSpace ℝ (Fin m)) : ℝ := φ ‖x‖ * χ (radialVec a 1 x)

variable {a R : ℝ} {φ : ℝ → ℝ} {χ : EuclideanSpace ℝ (Fin m) → ℝ}

/-- A test function supported in `(a, R)` vanishes on `(-∞, a]`. -/
theorem eq_zero_of_le (hφs : tsupport φ ⊆ Ioo a R) {t : ℝ} (ht : t ≤ a) : φ t = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => absurd (hφs h).1 (not_lt.2 ht)

theorem contDiff_comp_norm (ha : 0 < a) (hφ : ContDiff ℝ ∞ φ) (hφs : tsupport φ ⊆ Ioo a R) :
    ContDiff ℝ ∞ fun x : EuclideanSpace ℝ (Fin m) => φ ‖x‖ := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · have hev : ∀ᶠ y in 𝓝 (0 : EuclideanSpace ℝ (Fin m)), φ ‖y‖ = 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin m)) ha] with y hy
      exact eq_zero_of_le hφs (le_of_lt (mem_ball_zero_iff.1 hy))
    exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const hev
  · exact hφ.contDiffAt.comp x (contDiffAt_norm ℝ hx)

theorem polarTest_contDiff (ha : 0 < a) (hφ : ContDiff ℝ ∞ φ) (hφs : tsupport φ ⊆ Ioo a R)
    (hχ : ContDiff ℝ ∞ χ) : ContDiff ℝ ∞ (polarTest (m := m) a φ χ) :=
  (contDiff_comp_norm ha hφ hφs).mul (hχ.comp (radialVec_contDiff ha 1))

/-- The polar test function vanishes on the ball of radius `a`. -/
theorem polarTest_eq_zero_of_norm_le (hφs : tsupport φ ⊆ Ioo a R)
    {x : EuclideanSpace ℝ (Fin m)} (hx : ‖x‖ ≤ a) : polarTest a φ χ x = 0 := by
  rw [polarTest, eq_zero_of_le hφs hx, zero_mul]

/-- The support of the polar test function sits inside the compact annulus determined by the
support of `φ`. -/
theorem polarTest_tsupport :
    tsupport (polarTest (m := m) a φ χ) ⊆ {x : EuclideanSpace ℝ (Fin m) | ‖x‖ ∈ tsupport φ} := by
  refine closure_minimal ?_ (isClosed_tsupport φ |>.preimage continuous_norm)
  intro x hx
  have hne : φ ‖x‖ * χ (radialVec a 1 x) ≠ 0 := hx
  exact subset_closure fun h => hne (by rw [h, zero_mul])

theorem isCompact_norm_preimage (hφs : tsupport φ ⊆ Ioo a R) :
    IsCompact {x : EuclideanSpace ℝ (Fin m) | ‖x‖ ∈ tsupport φ} := by
  refine Metric.isCompact_of_isClosed_isBounded
    ((isClosed_tsupport φ).preimage continuous_norm) ?_
  refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨R, fun x hx => ?_⟩
  exact mem_closedBall_zero_iff.2 (le_of_lt (hφs hx).2)

theorem polarTest_hasCompactSupport (hφs : tsupport φ ⊆ Ioo a R) :
    HasCompactSupport (polarTest (m := m) a φ χ) :=
  IsCompact.of_isClosed_subset (isCompact_norm_preimage hφs) isClosed_closure
    polarTest_tsupport

theorem polarTest_tsupport_subset_ball (hφs : tsupport φ ⊆ Ioo a R) :
    tsupport (polarTest (m := m) a φ χ) ⊆ ball (0 : EuclideanSpace ℝ (Fin m)) R := fun _ hx =>
  mem_ball_zero_iff.2 (hφs (polarTest_tsupport hx)).2


/-! ### Evaluation of the polar test function along rays -/

theorem polarTest_smul (ha : 0 < a) (hφs : tsupport φ ⊆ Ioo a R) {t : ℝ} (ht : 0 < t)
    {w : EuclideanSpace ℝ (Fin m)} (hw : ‖w‖ = 1) : polarTest a φ χ (t • w) = φ t * χ w := by
  have hnorm : ‖t • w‖ = t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, hw, mul_one]
  rcases le_or_gt a t with hat | hta
  · have hr : radialVec a 1 (t • w) = w := by
      rw [radialVec_smul ha 1 hat w hw, pow_one, inv_mul_cancel₀ ht.ne', one_smul]
    rw [polarTest, hnorm, hr]
  · rw [polarTest, hnorm, eq_zero_of_le hφs hta.le, zero_mul, zero_mul]

/-- Off the support of `φ` the polar test function vanishes identically near `t • w`. -/
theorem fderiv_polarTest_eq_zero (hφs : tsupport φ ⊆ Ioo a R) {t : ℝ} (ht : 0 < t)
    (hta : t < a) {w : EuclideanSpace ℝ (Fin m)} (hw : ‖w‖ = 1) :
    fderiv ℝ (polarTest a φ χ) (t • w) = 0 := by
  have hnorm : ‖t • w‖ = t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, hw, mul_one]
  have hev : (polarTest (m := m) a φ χ) =ᶠ[𝓝 (t • w)] fun _ => (0 : ℝ) := by
    filter_upwards [Metric.ball_mem_nhds (t • w) (sub_pos.2 hta)] with y hy
    have h1 : ‖y - t • w‖ < a - t := by
      rw [← dist_eq_norm]
      exact mem_ball.1 hy
    have h2 : ‖y‖ ≤ a := by
      have := norm_add_le (y - t • w) (t • w)
      rw [sub_add_cancel, hnorm] at this
      linarith
    exact polarTest_eq_zero_of_norm_le hφs h2
  rw [hev.fderiv_eq]
  exact fderiv_const_apply 0

theorem deriv_eq_zero_of_lt (hφs : tsupport φ ⊆ Ioo a R) {t : ℝ} (hta : t < a) :
    deriv φ t = 0 := by
  have hev : φ =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds hta] with s hs
    exact eq_zero_of_le hφs hs.le
  rw [hev.deriv_eq]
  exact deriv_const t 0

/-- The radial derivative of the polar test function. -/
theorem fderiv_polarTest_dir (ha : 0 < a) (hφ : ContDiff ℝ ∞ φ) (hφs : tsupport φ ⊆ Ioo a R)
    (hχ : ContDiff ℝ ∞ χ) {t : ℝ} (ht : 0 < t) {w : EuclideanSpace ℝ (Fin m)} (hw : ‖w‖ = 1) :
    fderiv ℝ (polarTest a φ χ) (t • w) w = deriv φ t * χ w := by
  have hcd := polarTest_contDiff ha hφ hφs hχ
  have h1 : HasDerivAt (fun s : ℝ => s • w) w t := by
    simpa using (hasDerivAt_id t).smul_const w
  have h2 : HasDerivAt (fun s : ℝ => polarTest a φ χ (s • w))
      (fderiv ℝ (polarTest a φ χ) (t • w) w) t :=
    ((hcd.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt t h1
  have heq : (fun s : ℝ => φ s * χ w) =ᶠ[𝓝 t] fun s : ℝ => polarTest a φ χ (s • w) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact (polarTest_smul ha hφs hs hw).symm
  have h3 : HasDerivAt (fun s : ℝ => φ s * χ w)
      (fderiv ℝ (polarTest a φ χ) (t • w) w) t := h2.congr_of_eventuallyEq heq
  have h4 : HasDerivAt (fun s : ℝ => φ s * χ w) (deriv φ t * χ w) t :=
    ((hφ.differentiable (by simp)).differentiableAt.hasDerivAt).mul_const (χ w)
  exact h3.unique h4

/-- The derivative of the polar test function in the direction of the divergence-free radial
field. -/
theorem fderiv_polarTest_radialVec (ha : 0 < a) (hφ : ContDiff ℝ ∞ φ)
    (hφs : tsupport φ ⊆ Ioo a R) (hχ : ContDiff ℝ ∞ χ) {t : ℝ} (ht : 0 < t)
    {w : EuclideanSpace ℝ (Fin m)} (hw : ‖w‖ = 1) :
    fderiv ℝ (polarTest a φ χ) (t • w) (radialVec a m (t • w))
      = ((t ^ m)⁻¹ * t) * (deriv φ t * χ w) := by
  rcases le_or_gt a t with hat | hta
  · rw [radialVec_smul ha m hat w hw, ContinuousLinearMap.map_smul, smul_eq_mul,
      fderiv_polarTest_dir ha hφ hφs hχ ht hw]
  · rw [fderiv_polarTest_eq_zero hφs ht hta hw, deriv_eq_zero_of_lt hφs hta]
    simp

/-- The pairing of the gradient with the radial field against the polar test function. -/
theorem inner_radialVec_mul_polarTest (ha : 0 < a) (hφs : tsupport φ ⊆ Ioo a R)
    (G : EuclideanSpace ℝ (Fin m)) {t : ℝ} (ht : 0 < t) {w : EuclideanSpace ℝ (Fin m)}
    (hw : ‖w‖ = 1) :
    inner ℝ G (radialVec a m (t • w)) * polarTest a φ χ (t • w)
      = ((t ^ m)⁻¹ * t) * (inner ℝ G w * (φ t * χ w)) := by
  rcases le_or_gt a t with hat | hta
  · rw [radialVec_smul ha m hat w hw, real_inner_smul_right,
      polarTest_smul ha hφs ht hw]
    ring
  · rw [polarTest_smul ha hφs ht hw, eq_zero_of_le hφs hta.le]
    ring

/-- The polar test function kills the divergence of the radial field. -/
theorem polarTest_mul_divergence (ha : 0 < a) (hφs : tsupport φ ⊆ Ioo a R)
    (x : EuclideanSpace ℝ (Fin m)) :
    polarTest a φ χ x
        * (∑ i, fderiv ℝ (radialVec a m) x (EuclideanSpace.single i 1) i) = 0 := by
  rcases le_or_gt a ‖x‖ with hx | hx
  · rw [divergence_radialVec ha m hx, sub_self, zero_mul, mul_zero]
  · rw [polarTest_eq_zero_of_norm_le hφs hx.le, zero_mul]


/-! ### The polar identity -/

/-- The cancellation of the polar weight against the radial field: `r^{m-1} · r^{1-m} = 1`. -/
theorem pow_weight_cancel (hm : 1 ≤ m) {r : ℝ} (hr : 0 < r) :
    r ^ (m - 1) * ((r ^ m)⁻¹ * r) = 1 := by
  have hne : (r : ℝ) ^ m ≠ 0 := pow_ne_zero _ hr.ne'
  have h : r ^ (m - 1) * r = r ^ m := by
    rw [← pow_succ]
    congr 1
    omega
  calc r ^ (m - 1) * ((r ^ m)⁻¹ * r) = (r ^ (m - 1) * r) * (r ^ m)⁻¹ := by ring
    _ = r ^ m * (r ^ m)⁻¹ := by rw [h]
    _ = 1 := mul_inv_cancel₀ hne

/-- **The radial pairing.**  `radialPairing R u g φ w = ∫_0^R (u(r w) φ'(r) + ⟪g(r w), w⟫ φ(r))`,
the quantity which has to vanish for almost every direction `w`. -/
def radialPairing (R : ℝ) (u : EuclideanSpace ℝ (Fin m) → ℝ)
    (g : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) (φ : ℝ → ℝ)
    (w : EuclideanSpace ℝ (Fin m)) : ℝ :=
  ∫ r in Ioo (0 : ℝ) R, (u (r • w) * deriv φ r + inner ℝ (g (r • w)) w * φ r)

variable {u : EuclideanSpace ℝ (Fin m) → ℝ}
  {g : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}

/-- The angular integrand of the polar identity is `radialPairing · χ`. -/
theorem angular_integral_eq (hm : 1 ≤ m) (ha : 0 < a) (hφ : ContDiff ℝ ∞ φ)
    (hφs : tsupport φ ⊆ Ioo a R) (hχ : ContDiff ℝ ∞ χ) {w : EuclideanSpace ℝ (Fin m)}
    (hw : ‖w‖ = 1) :
    (∫ r in Ioo (0 : ℝ) R, r ^ (m - 1) *
        (u (r • w) * fderiv ℝ (polarTest a φ χ) (r • w) (radialVec a m (r • w))
          + inner ℝ (g (r • w)) (radialVec a m (r • w)) * polarTest a φ χ (r • w)))
      = radialPairing R u g φ w * χ w := by
  rw [radialPairing, ← integral_mul_const]
  refine setIntegral_congr_fun measurableSet_Ioo fun r hr => ?_
  have hr0 : (0 : ℝ) < r := hr.1
  rw [fderiv_polarTest_radialVec ha hφ hφs hχ hr0 hw,
    inner_radialVec_mul_polarTest ha hφs (g (r • w)) hr0 hw]
  have hcancel := pow_weight_cancel hm hr0
  have hring : r ^ (m - 1) * (u (r • w) * (((r ^ m)⁻¹ * r) * (deriv φ r * χ w))
        + ((r ^ m)⁻¹ * r) * (inner ℝ (g (r • w)) w * (φ r * χ w)))
      = (r ^ (m - 1) * ((r ^ m)⁻¹ * r))
        * ((u (r • w) * deriv φ r + inner ℝ (g (r • w)) w * φ r) * χ w) := by ring
  rw [hring, hcancel, one_mul]

open RobinCaps.ThinDomain in
/-- **The polar identity.**  For a weak `H¹` function on the ball, every test function `φ`
supported in `(a, R)` and every smooth `χ` on `E`, the radial pairing is orthogonal to `χ` on
the unit sphere. -/
theorem integral_radialPairing_mul_eq_zero (hm : 1 ≤ m)
    (hu : MemLp u 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) R)))
    (hg : MemLp g 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) R)))
    (hwg : HasWeakGrad (ball (0 : EuclideanSpace ℝ (Fin m)) R) u g)
    (ha : 0 < a) (hφ : ContDiff ℝ ∞ φ) (hφs : tsupport φ ⊆ Ioo a R) (hχ : ContDiff ℝ ∞ χ) :
    ∫ w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      radialPairing R u g φ (w : EuclideanSpace ℝ (Fin m)) * χ (w : EuclideanSpace ℝ (Fin m))
        ∂(sphereMeasure m) = 0 := by
  have hcd : ContDiff ℝ ∞ (polarTest (m := m) a φ χ) := polarTest_contDiff ha hφ hφs hχ
  have hcs : HasCompactSupport (polarTest (m := m) a φ χ) := polarTest_hasCompactSupport hφs
  have hsb : tsupport (polarTest (m := m) a φ χ) ⊆ ball (0 : EuclideanSpace ℝ (Fin m)) R :=
    polarTest_tsupport_subset_ball hφs
  have hX : ContDiff ℝ ∞ (radialVec (m := m) a m) := radialVec_contDiff ha m
  have hD1 := HasWeakGrad.integral_inner_vectorField hu hg hwg hcd hcs hsb hX
  have hdivzero : ∀ x : EuclideanSpace ℝ (Fin m),
      u x * polarTest a φ χ x
        * (∑ i, fderiv ℝ (radialVec a m) x (EuclideanSpace.single i 1) i) = 0 := by
    intro x
    rw [mul_assoc, polarTest_mul_divergence ha hφs x, mul_zero]
  rw [show (∫ x in ball (0 : EuclideanSpace ℝ (Fin m)) R, u x * polarTest a φ χ x
      * (∑ i, fderiv ℝ (radialVec a m) x (EuclideanSpace.single i 1) i)) = 0 by
    simp only [hdivzero, integral_zero], sub_zero] at hD1
  have hint1 : IntegrableOn (fun x => u x * fderiv ℝ (polarTest a φ χ) x (radialVec a m x))
      (ball (0 : EuclideanSpace ℝ (Fin m)) R) :=
    integrable_mul_fderiv_vectorField hu hcd hcs hX
  have hint2 : IntegrableOn
      (fun x => inner ℝ (g x) (radialVec a m x) * polarTest a φ χ x)
      (ball (0 : EuclideanSpace ℝ (Fin m)) R) := integrable_inner_mul_test hg hcd hcs hX
  have hadd : (∫ x in ball (0 : EuclideanSpace ℝ (Fin m)) R,
        (u x * fderiv ℝ (polarTest a φ χ) x (radialVec a m x)
          + inner ℝ (g x) (radialVec a m x) * polarTest a φ χ x))
      = (∫ x in ball (0 : EuclideanSpace ℝ (Fin m)) R,
          u x * fderiv ℝ (polarTest a φ χ) x (radialVec a m x))
        + ∫ x in ball (0 : EuclideanSpace ℝ (Fin m)) R,
          inner ℝ (g x) (radialVec a m x) * polarTest a φ χ x := integral_add hint1 hint2
  have hsum0 : ∫ x in ball (0 : EuclideanSpace ℝ (Fin m)) R,
      (u x * fderiv ℝ (polarTest a φ χ) x (radialVec a m x)
        + inner ℝ (g x) (radialVec a m x) * polarTest a φ χ x) = 0 := by
    rw [hadd, hD1]
    ring
  have hintsum : IntegrableOn
      (fun x => u x * fderiv ℝ (polarTest a φ χ) x (radialVec a m x)
        + inner ℝ (g x) (radialVec a m x) * polarTest a φ χ x)
      (ball (0 : EuclideanSpace ℝ (Fin m)) R) := hint1.add hint2
  rw [integral_ball_polar_symm hm hintsum] at hsum0
  rw [← hsum0]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  exact (angular_integral_eq hm ha hφ hφs hχ (mem_sphere_zero_iff_norm.1 w.2)).symm


open RobinCaps.ThinDomain in
/-- The radial pairing is an integrable function of the direction. -/
theorem integrable_radialPairing (hm : 1 ≤ m)
    (hu : MemLp u 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) R)))
    (hg : MemLp g 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) R)))
    (ha : 0 < a) (hφ : ContDiff ℝ ∞ φ) (hφs : tsupport φ ⊆ Ioo a R) :
    Integrable (fun w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      radialPairing R u g φ (w : EuclideanSpace ℝ (Fin m))) (sphereMeasure m) := by
  have hχ : ContDiff ℝ ∞ (fun _ : EuclideanSpace ℝ (Fin m) => (1 : ℝ)) := contDiff_const
  have hcd := polarTest_contDiff ha hφ hφs hχ
  have hcs := polarTest_hasCompactSupport (χ := fun _ : EuclideanSpace ℝ (Fin m) => (1 : ℝ)) hφs
  have hX := radialVec_contDiff (m := m) ha m
  have hintsum : IntegrableOn
      (fun x => u x * fderiv ℝ (polarTest a φ (fun _ => 1)) x (radialVec a m x)
        + inner ℝ (g x) (radialVec a m x) * polarTest a φ (fun _ => 1) x)
      (ball (0 : EuclideanSpace ℝ (Fin m)) R) :=
    (integrable_mul_fderiv_vectorField hu hcd hcs hX).add (integrable_inner_mul_test hg hcd hcs hX)
  refine (integrable_ball_angular hm hintsum).congr (Eventually.of_forall fun w => ?_)
  dsimp only
  rw [angular_integral_eq hm ha hφ hφs hχ (mem_sphere_zero_iff_norm.1 w.2)]
  ring

open RobinCaps.ThinDomain in
/-- **The radial pairing vanishes for almost every direction.**  This is the polar identity
combined with the duality between `L¹` functions on the sphere and smooth functions on `E`. -/
theorem radialPairing_ae_eq_zero (hm : 1 ≤ m)
    (hu : MemLp u 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) R)))
    (hg : MemLp g 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) R)))
    (hwg : HasWeakGrad (ball (0 : EuclideanSpace ℝ (Fin m)) R) u g)
    (ha : 0 < a) (hφ : ContDiff ℝ ∞ φ) (hφs : tsupport φ ⊆ Ioo a R) :
    ∀ᵐ w ∂(sphereMeasure m),
      radialPairing R u g φ ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
        EuclideanSpace ℝ (Fin m)) = 0 := by
  have hcl : IsClosed (sphere (0 : EuclideanSpace ℝ (Fin m)) 1) := isClosed_sphere
  have hA := ae_eq_zero_of_forall_contDiff_mul_eq_zero hcl
    (σ := sphereMeasure m)
    (A := fun w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      radialPairing R u g φ (w : EuclideanSpace ℝ (Fin m)))
    (integrable_radialPairing hm hu hg ha hφ hφs)
    (fun χ' hχ' => integral_radialPairing_mul_eq_zero hm hu hg hwg ha hφ hφs hχ')
  filter_upwards [hA] with w hw using hw


/-! ### Integrability of the radial slices -/

/-- Transfer of integrability from the subtype measure `volumeIoiPow k` to the weighted
Lebesgue integral on `(0, ∞)`. -/
theorem integrableOn_of_integrable_volumeIoiPow (k : ℕ) {G : ℝ → ℝ}
    (h : Integrable (fun r : Ioi (0 : ℝ) => G (r : ℝ)) (Measure.volumeIoiPow k)) :
    IntegrableOn (fun r : ℝ => r ^ k * G r) (Ioi (0 : ℝ)) := by
  rw [Measure.volumeIoiPow,
    integrable_withDensity_iff_integrable_smul' (by fun_prop) (by simp)] at h
  rw [integrableOn_iff_comap_subtypeVal measurableSet_Ioi]
  refine (integrable_congr ?_).2 h
  refine .of_forall ?_
  rintro ⟨x, hx⟩
  have hx0 : (0 : ℝ) < x := hx
  simp [ENNReal.toReal_ofReal (pow_nonneg hx0.le k)]

open RobinCaps.ThinDomain in
/-- For almost every direction the weighted radial slice of an integrable function on the ball
is integrable on `(0, ∞)`. -/
theorem ae_integrableOn_radialSlice (hm : 1 ≤ m) {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf : IntegrableOn f (ball (0 : EuclideanSpace ℝ (Fin m)) R)) :
    ∀ᵐ w ∂(sphereMeasure m), IntegrableOn
      (fun r : ℝ => r ^ (m - 1) * (ball (0 : EuclideanSpace ℝ (Fin m)) R).indicator f
        (r • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) : EuclideanSpace ℝ (Fin m))))
      (Ioi (0 : ℝ)) := by
  haveI := nontrivial_euclidean hm
  have hF : Integrable ((ball (0 : EuclideanSpace ℝ (Fin m)) R).indicator f) :=
    hf.integrable_indicator measurableSet_ball
  have hprod := (integrable_polar_iff (volume : Measure (EuclideanSpace ℝ (Fin m))) _).2 hF
  have hrank : finrank ℝ (EuclideanSpace ℝ (Fin m)) - 1 = m - 1 := by rw [finrank_eq]
  rw [hrank] at hprod
  filter_upwards [hprod.prod_right_ae] with w hw
  exact integrableOn_of_integrable_volumeIoiPow (m - 1) hw

open RobinCaps.ThinDomain in
/-- **Almost every radial slice is integrable away from the origin.** -/
theorem ae_integrableOn_slice (hm : 1 ≤ m) {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf : IntegrableOn f (ball (0 : EuclideanSpace ℝ (Fin m)) R)) :
    ∀ᵐ w ∂(sphereMeasure m), ∀ ε ∈ Ioo (0 : ℝ) R, IntegrableOn
      (fun r : ℝ => f (r • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
        EuclideanSpace ℝ (Fin m)))) (Ioo ε R) := by
  filter_upwards [ae_integrableOn_radialSlice (R := R) hm hf] with w hw ε hε
  have hεpos : (0 : ℝ) < ε := hε.1
  have hsub : Ioo ε R ⊆ Ioi (0 : ℝ) := fun r hr => lt_trans hεpos hr.1
  have h2 := hw.mono_set hsub
  have hmeas : AEStronglyMeasurable (fun r : ℝ => (r ^ (m - 1))⁻¹)
      (volume.restrict (Ioo ε R)) := ((measurable_id.pow_const (m - 1)).inv).aestronglyMeasurable
  have heq : ∀ r ∈ Ioo ε R,
      (r ^ (m - 1))⁻¹ * (r ^ (m - 1) * (ball (0 : EuclideanSpace ℝ (Fin m)) R).indicator f
        (r • (w : EuclideanSpace ℝ (Fin m))))
      = f (r • (w : EuclideanSpace ℝ (Fin m))) := by
    intro r hr
    have hr0 : (0 : ℝ) < r := lt_trans hεpos hr.1
    have hmem : r • (w : EuclideanSpace ℝ (Fin m)) ∈ ball (0 : EuclideanSpace ℝ (Fin m)) R := by
      simpa [mem_ball_zero_iff, norm_smul_sphere hr0 w] using hr.2
    rw [Set.indicator_of_mem hmem, inv_mul_cancel_left₀ (pow_ne_zero _ hr0.ne')]
  have hae : (fun r : ℝ => (r ^ (m - 1))⁻¹ * (r ^ (m - 1) *
        (ball (0 : EuclideanSpace ℝ (Fin m)) R).indicator f
          (r • (w : EuclideanSpace ℝ (Fin m)))))
      =ᵐ[volume.restrict (Ioo ε R)]
      fun r : ℝ => f (r • (w : EuclideanSpace ℝ (Fin m))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr using heq r hr
  have hmeas2 : AEStronglyMeasurable
      (fun r : ℝ => f (r • (w : EuclideanSpace ℝ (Fin m)))) (volume.restrict (Ioo ε R)) :=
    (hmeas.mul h2.aestronglyMeasurable).congr hae
  refine Integrable.mono' (h2.norm.const_mul ((ε ^ (m - 1))⁻¹)) hmeas2 ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  have hr0 : (0 : ℝ) < r := lt_trans hεpos hr.1
  have hle : ε ^ (m - 1) ≤ r ^ (m - 1) := by
    gcongr
    exact le_of_lt hr.1
  have hpos : (0 : ℝ) < ε ^ (m - 1) := pow_pos hεpos _
  have hinv : (r ^ (m - 1))⁻¹ ≤ (ε ^ (m - 1))⁻¹ := by
    rw [inv_le_inv₀ (lt_of_lt_of_le hpos hle) hpos]
    exact hle
  rw [← heq r hr, norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hnorm : (0 : ℝ) ≤ ‖r ^ (m - 1) * (ball (0 : EuclideanSpace ℝ (Fin m)) R).indicator f
      (r • (w : EuclideanSpace ℝ (Fin m)))‖ := norm_nonneg _
  exact mul_le_mul_of_nonneg_right hinv hnorm


/-! ### One-dimensional helpers -/

/-- Two set integrals agree when the integrand is supported in the smaller set. -/
theorem setIntegral_eq_of_subset {s t : Set ℝ} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hts : t ⊆ s) {f : ℝ → ℝ} (h : ∀ x, x ∉ t → f x = 0) :
    ∫ x in s, f x = ∫ x in t, f x := by
  rw [← integral_indicator hs, ← integral_indicator ht]
  congr 1
  funext x
  by_cases hx : x ∈ t
  · rw [Set.indicator_of_mem (hts hx), Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx]
    by_cases hxs : x ∈ s
    · rw [Set.indicator_of_mem hxs, h x hx]
    · rw [Set.indicator_of_notMem hxs]

/-- The derivative of a function vanishes off its support. -/
theorem deriv_eq_zero_of_notMem_tsupport {Θ : ℝ → ℝ} {r : ℝ} (h : r ∉ tsupport Θ) :
    deriv Θ r = 0 :=
  Function.notMem_support.1 fun hc => h (support_deriv_subset hc)

/-- The one-dimensional weak derivative localizes to smaller intervals. -/
theorem hasWeakDeriv_mono {a a' b : ℝ} (haa : a ≤ a') {v G : ℝ → ℝ}
    (h : RobinCaps.Sobolev.HasWeakDeriv a b v G) : RobinCaps.Sobolev.HasWeakDeriv a' b v G := by
  intro Θ hΘ hΘc hΘs
  have hsub : Ioo a' b ⊆ Ioo a b := Ioo_subset_Ioo haa le_rfl
  have hL : ∫ x in Ioo a b, v x * deriv Θ x = ∫ x in Ioo a' b, v x * deriv Θ x := by
    refine setIntegral_eq_of_subset measurableSet_Ioo measurableSet_Ioo hsub fun x hx => ?_
    rw [deriv_eq_zero_of_notMem_tsupport fun hc => hx (hΘs hc), mul_zero]
  have hR : ∫ x in Ioo a b, G x * Θ x = ∫ x in Ioo a' b, G x * Θ x := by
    refine setIntegral_eq_of_subset measurableSet_Ioo measurableSet_Ioo hsub fun x hx => ?_
    rw [image_eq_zero_of_notMem_tsupport fun hc => hx (hΘs hc), mul_zero]
  rw [← hL, ← hR]
  exact h Θ hΘ hΘc (hΘs.trans hsub)

/-- The exhausting sequence of inner radii of `(0, R)`. -/
def innerRadius (R : ℝ) (n : ℕ) : ℝ := R / (n + 2)

theorem innerRadius_mem (hR : 0 < R) (n : ℕ) : innerRadius R n ∈ Ioo (0 : ℝ) R := by
  have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  refine ⟨div_pos hR hn, ?_⟩
  rw [innerRadius, div_lt_iff₀ hn]
  nlinarith

theorem exists_innerRadius_lt (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, innerRadius R n < ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (R / ε)
  refine ⟨n, ?_⟩
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  rw [innerRadius, div_lt_iff₀ hn2]
  have : R / ε < (n : ℝ) + 2 := by linarith
  rw [div_lt_iff₀ hε] at this
  nlinarith


/-! ### Deliverable 2: the radial ACL property -/

set_option maxHeartbeats 2000000 in
open RobinCaps.ThinDomain RobinCaps.Sobolev in
/-- **The radial ACL property.**  For almost every direction `w` of the unit sphere, the radial
slice `r ↦ u (r w)` has `r ↦ ⟪∇u (r w), w⟫` as a weak derivative on every interval `(ε, R)`
with `0 < ε < R`. -/
theorem radialSlice_ae_of_hasWeakGrad (hm : 1 ≤ m) (hR : 0 < R)
    (hu : MemLp u 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) R)))
    (hg : MemLp g 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) R)))
    (hwg : HasWeakGrad (ball (0 : EuclideanSpace ℝ (Fin m)) R) u g) :
    ∀ᵐ w ∂(sphereMeasure m), ∀ ε ∈ Ioo (0 : ℝ) R,
      HasWeakDeriv ε R (fun r => u (r • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
          EuclideanSpace ℝ (Fin m))))
        (fun r => inner ℝ (g (r • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
          EuclideanSpace ℝ (Fin m)))) ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
          EuclideanSpace ℝ (Fin m))) := by
  classical
  haveI : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have huint : IntegrableOn u (ball (0 : EuclideanSpace ℝ (Fin m)) R) := hu.integrable one_le_two
  have hgint : ∀ i : Fin m, IntegrableOn (fun x => g x i)
      (ball (0 : EuclideanSpace ℝ (Fin m)) R) := fun i =>
    (memLp_two_comp hg i).integrable one_le_two
  -- the countable family of test functions
  have hex : ∀ p : ℕ × (ℚ × ℚ × ℕ), ∃ θ : ℝ → ℝ, ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧
      tsupport θ ⊆ Ioo (innerRadius R p.1) R ∧
      ((innerRadius R p.1 < (p.2.1 : ℝ) ∧ ((p.2.1 : ℝ) < (p.2.2.1 : ℝ))
          ∧ ((p.2.2.1 : ℝ) < R)) →
        deriv θ = fun x => idxBump p.2 x
          - (∫ y, idxBump p.2 y) * bump (innerRadius_mem hR p.1).2 x) := by
    intro p
    set A : ℝ := innerRadius R p.1 with hA
    have hab : A < R := (innerRadius_mem hR p.1).2
    by_cases hP : A < (p.2.1 : ℝ) ∧ ((p.2.1 : ℝ) < (p.2.2.1 : ℝ)) ∧ ((p.2.2.1 : ℝ) < R)
    · obtain ⟨h1, h2, h3⟩ := hP
      have hbs : ContDiff ℝ ∞ (idxBump p.2) := idxBump_contDiff h2
      have hbc : HasCompactSupport (idxBump p.2) := idxBump_hasCompactSupport h2
      have hbt : tsupport (idxBump p.2) ⊆ Ioo A R := by
        rw [idxBump_tsupport h2]
        exact Icc_subset_Ioo h1 h3
      have hρs : ContDiff ℝ ∞ (bump hab) := bump_contDiff hab
      have hρc : HasCompactSupport (bump hab) := bump_hasCompactSupport hab
      have hρt : tsupport (bump hab) ⊆ Ioo A R := bump_tsupport hab
      have hψs : ContDiff ℝ ∞
          (fun x => idxBump p.2 x - (∫ y, idxBump p.2 y) * bump hab x) :=
        hbs.sub (contDiff_const.mul hρs)
      have hψc : HasCompactSupport
          (fun x => idxBump p.2 x - (∫ y, idxBump p.2 y) * bump hab x) :=
        hbc.sub hρc.mul_left
      have hψt : tsupport (fun x => idxBump p.2 x - (∫ y, idxBump p.2 y) * bump hab x)
          ⊆ Ioo A R :=
        (tsupport_sub_const_mul_subset _ _ _).trans (union_subset hbt hρt)
      have hint : ∫ x, (idxBump p.2 x - (∫ y, idxBump p.2 y) * bump hab x) = 0 := by
        rw [integral_sub (hbs.continuous.integrable_of_hasCompactSupport hbc)
            ((continuous_const.mul hρs.continuous).integrable_of_hasCompactSupport hρc.mul_left),
          integral_const_mul, bump_integral hab, mul_one, sub_self]
      obtain ⟨Θ, hΘ1, hΘ2, hΘ3, hΘ4⟩ := exists_test_primitive hab hψs hψc hψt hint
      exact ⟨Θ, hΘ1, hΘ2, hΘ3, fun _ => hΘ4⟩
    · refine ⟨fun _ => 0, contDiff_const, HasCompactSupport.zero, ?_, fun h => absurd h hP⟩
      simp [tsupport]
  choose θ hθc hθcs hθts hθd using hex
  -- the radial pairing vanishes for almost every direction, for every member of the family
  have hzero : ∀ᵐ w ∂(sphereMeasure m), ∀ p : ℕ × (ℚ × ℚ × ℕ),
      radialPairing R u g (θ p) ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
        EuclideanSpace ℝ (Fin m)) = 0 := by
    rw [ae_all_iff]
    intro p
    exact radialPairing_ae_eq_zero hm hu hg hwg (innerRadius_mem hR p.1).1 (hθc p) (hθts p)
  -- the slice integrability
  have hslice_g : ∀ᵐ w ∂(sphereMeasure m), ∀ i : Fin m, ∀ ε ∈ Ioo (0 : ℝ) R,
      IntegrableOn (fun r : ℝ => g (r • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
        EuclideanSpace ℝ (Fin m))) i) (Ioo ε R) :=
    ae_all_iff.2 fun i => ae_integrableOn_slice hm (hgint i)
  filter_upwards [ae_integrableOn_slice (R := R) hm huint, hslice_g, hzero]
    with w hwu hwg' hwz
  -- integrability of the radial derivative slice
  have hwi : ∀ ε ∈ Ioo (0 : ℝ) R, IntegrableOn
      (fun r : ℝ => inner ℝ (g (r • (w : EuclideanSpace ℝ (Fin m))))
        (w : EuclideanSpace ℝ (Fin m))) (Ioo ε R) := by
    intro ε hε
    have hsum : IntegrableOn (fun r : ℝ =>
        ∑ i, g (r • (w : EuclideanSpace ℝ (Fin m))) i * (w : EuclideanSpace ℝ (Fin m)) i)
        (Ioo ε R) :=
      integrable_finset_sum (μ := volume.restrict (Ioo ε R)) Finset.univ
        fun i _ => (hwg' i ε hε).mul_const _
    refine hsum.congr (Eventually.of_forall fun r => ?_)
    exact (inner_eq_sum (g (r • (w : EuclideanSpace ℝ (Fin m))))
      (w : EuclideanSpace ℝ (Fin m))).symm
  intro ε hε
  obtain ⟨n, hn⟩ := exists_innerRadius_lt R hε.1
  refine hasWeakDeriv_mono (le_of_lt hn) ?_
  have hab : innerRadius R n < R := (innerRadius_mem hR n).2
  have hmem : innerRadius R n ∈ Ioo (0 : ℝ) R := innerRadius_mem hR n
  refine hasWeakDeriv_of_idxBump hab (hwu _ hmem) (hwi _ hmem) ?_
  intro k h1 h2 h3
  -- the identity for the primitive of the `k`-th bump
  have hP : innerRadius R (n, k).1 < ((n, k).2.1 : ℝ)
      ∧ (((n, k).2.1 : ℝ) < ((n, k).2.2.1 : ℝ)) ∧ (((n, k).2.2.1 : ℝ) < R) := ⟨h1, h2, h3⟩
  have hderiv : deriv (θ (n, k))
      = fun x => idxBump k x - (∫ y, idxBump k y) * bump hab x := hθd (n, k) hP
  have hΘc := hθc (n, k)
  have hΘcs := hθcs (n, k)
  have hΘts := hθts (n, k)
  have h0 := hwz (n, k)
  rw [radialPairing] at h0
  -- restrict the pairing to `(innerRadius R n, R)`
  have hrestrict : ∫ r in Ioo (0 : ℝ) R,
      (u (r • (w : EuclideanSpace ℝ (Fin m))) * deriv (θ (n, k)) r
        + inner ℝ (g (r • (w : EuclideanSpace ℝ (Fin m))))
          (w : EuclideanSpace ℝ (Fin m)) * θ (n, k) r)
      = ∫ r in Ioo (innerRadius R n) R,
      (u (r • (w : EuclideanSpace ℝ (Fin m))) * deriv (θ (n, k)) r
        + inner ℝ (g (r • (w : EuclideanSpace ℝ (Fin m))))
          (w : EuclideanSpace ℝ (Fin m)) * θ (n, k) r) := by
    refine setIntegral_eq_of_subset measurableSet_Ioo measurableSet_Ioo
      (Ioo_subset_Ioo hmem.1.le le_rfl) fun r hr => ?_
    rw [deriv_eq_zero_of_notMem_tsupport fun hc => hr (hΘts hc),
      image_eq_zero_of_notMem_tsupport fun hc => hr (hΘts hc), mul_zero, mul_zero, add_zero]
  rw [hrestrict] at h0
  -- split the two terms
  have hI1 : IntegrableOn (fun r : ℝ => u (r • (w : EuclideanSpace ℝ (Fin m)))
      * deriv (θ (n, k)) r) (Ioo (innerRadius R n) R) := by
    refine integrableOn_mul_test (hwu _ hmem) ?_ ?_
    · rw [hderiv]
      exact ((idxBump_contDiff h2).sub (contDiff_const.mul (bump_contDiff hab))).continuous
    · rw [hderiv]
      exact (idxBump_hasCompactSupport h2).sub (bump_hasCompactSupport hab).mul_left
  have hI2 : IntegrableOn (fun r : ℝ => inner ℝ (g (r • (w : EuclideanSpace ℝ (Fin m))))
      (w : EuclideanSpace ℝ (Fin m)) * θ (n, k) r) (Ioo (innerRadius R n) R) :=
    integrableOn_mul_test (hwi _ hmem) hΘc.continuous hΘcs
  rw [integral_add hI1 hI2] at h0
  -- the weak derivative of the primitive of the radial derivative
  have hmid : ((innerRadius R n + R) / 2) ∈ Icc (innerRadius R n) R :=
    ⟨by linarith, by linarith⟩
  have hprim := hasWeakDeriv_primitive hab (hwi _ hmem) hmid (θ (n, k)) hΘc hΘcs hΘts
  -- assemble
  have hIP : IntegrableOn (fun r : ℝ =>
      (∫ t in ((innerRadius R n + R) / 2)..r,
        inner ℝ (g (t • (w : EuclideanSpace ℝ (Fin m)))) (w : EuclideanSpace ℝ (Fin m)))
      * deriv (θ (n, k)) r) (Ioo (innerRadius R n) R) := by
    refine integrableOn_mul_test (integrableOn_primitive hab (hwi _ hmem)) ?_ ?_
    · rw [hderiv]
      exact ((idxBump_contDiff h2).sub (contDiff_const.mul (bump_contDiff hab))).continuous
    · rw [hderiv]
      exact (idxBump_hasCompactSupport h2).sub (bump_hasCompactSupport hab).mul_left
  simp only [hderiv] at h0 hI1 hIP hprim
  have hsplit : (∫ x in Ioo (innerRadius R n) R,
      (u (x • (w : EuclideanSpace ℝ (Fin m)))
        - ∫ t in ((innerRadius R n + R) / 2)..x,
          inner ℝ (g (t • (w : EuclideanSpace ℝ (Fin m)))) (w : EuclideanSpace ℝ (Fin m)))
      * (idxBump k x - (∫ y, idxBump k y) * bump hab x))
      = (∫ x in Ioo (innerRadius R n) R, u (x • (w : EuclideanSpace ℝ (Fin m)))
          * (idxBump k x - (∫ y, idxBump k y) * bump hab x))
        - ∫ x in Ioo (innerRadius R n) R,
          (∫ t in ((innerRadius R n + R) / 2)..x,
            inner ℝ (g (t • (w : EuclideanSpace ℝ (Fin m)))) (w : EuclideanSpace ℝ (Fin m)))
          * (idxBump k x - (∫ y, idxBump k y) * bump hab x) := by
    rw [← integral_sub hI1 hIP]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    ring
  rw [hsplit, hprim]
  linarith [h0]


open RobinCaps.ThinDomain RobinCaps.Sobolev in
/-- **Deliverable 2, for an element of the weak Sobolev space `H¹(B_R)`.**  For almost every
direction `w`, the radial slice of `u` is a one-dimensional Sobolev function on every
`(ε, R)`, with weak derivative the radial component of the weak gradient. -/
theorem radialSlice_ae (hm : 1 ≤ m) (hR : 0 < R)
    (u : H1 (ball (0 : EuclideanSpace ℝ (Fin m)) R)) :
    ∀ᵐ w ∂(sphereMeasure m), ∀ ε ∈ Ioo (0 : ℝ) R,
      HasWeakDeriv ε R
        (fun r => u.toFun (r • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
          EuclideanSpace ℝ (Fin m))))
        (fun r => inner ℝ (u.grad (r • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
          EuclideanSpace ℝ (Fin m)))) ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
          EuclideanSpace ℝ (Fin m))) :=
  radialSlice_ae_of_hasWeakGrad hm hR u.memL2 u.grad_memL2 u.hasWeakGrad


/-! ### Translation of the one-dimensional weak derivative -/

theorem measurePreserving_addRight' (c : ℝ) :
    MeasurePreserving (fun x : ℝ => x + c) volume volume :=
  measurePreserving_add_right volume c

theorem measurableEmbedding_addRight' (c : ℝ) : MeasurableEmbedding (fun x : ℝ => x + c) :=
  (MeasurableEquiv.addRight c).measurableEmbedding

theorem setIntegral_translate (c : ℝ) (f : ℝ → ℝ) (s : Set ℝ) :
    ∫ x in (fun x : ℝ => x + c) ⁻¹' s, f (x + c) = ∫ y in s, f y :=
  (measurePreserving_addRight' c).setIntegral_preimage_emb (measurableEmbedding_addRight' c) f s

theorem integrableOn_translate {c : ℝ} {f : ℝ → ℝ} {s : Set ℝ} (h : IntegrableOn f s) :
    IntegrableOn (fun x => f (x + c)) ((fun x : ℝ => x + c) ⁻¹' s) :=
  ((measurePreserving_addRight' c).integrableOn_comp_preimage
    (measurableEmbedding_addRight' c)).2 h

theorem preimage_addRight_Ioo (a b c : ℝ) :
    (fun x : ℝ => x + c) ⁻¹' (Ioo a b) = Ioo (a - c) (b - c) := by
  ext x
  simp only [Set.mem_preimage, mem_Ioo, sub_lt_iff_lt_add, lt_sub_iff_add_lt]

/-- **Translation invariance of the one-dimensional weak derivative.** -/
theorem hasWeakDeriv_translate {a b c : ℝ} {v G : ℝ → ℝ}
    (h : RobinCaps.Sobolev.HasWeakDeriv a b v G) :
    RobinCaps.Sobolev.HasWeakDeriv (a - c) (b - c) (fun s => v (s + c)) (fun s => G (s + c)) := by
  intro φ hφ hφc hφs
  have hφ'c : ContDiff ℝ ∞ (fun y : ℝ => φ (y - c)) :=
    hφ.comp (contDiff_id.sub contDiff_const)
  have hφ'cs : HasCompactSupport (fun y : ℝ => φ (y - c)) :=
    hφc.comp_homeomorph (Homeomorph.subRight c)
  have hφ's : tsupport (fun y : ℝ => φ (y - c)) ⊆ Ioo a b := by
    have hclosed : IsClosed ((fun y : ℝ => y - c) ⁻¹' (tsupport φ)) :=
      (isClosed_tsupport φ).preimage (continuous_id.sub continuous_const)
    refine (closure_minimal (fun y hy => ?_) hclosed).trans (fun y hy => ?_)
    · exact subset_closure hy
    · have := hφs hy
      simp only [mem_Ioo] at this ⊢
      constructor <;> linarith [this.1, this.2]
  have hd : ∀ y : ℝ, deriv (fun z : ℝ => φ (z - c)) y = deriv φ (y - c) := fun y => by
    simpa using deriv_comp_sub_const φ c y
  have key := h (fun y : ℝ => φ (y - c)) hφ'c hφ'cs hφ's
  have hL : ∫ x in Ioo (a - c) (b - c), v (x + c) * deriv φ x
      = ∫ y in Ioo a b, v y * deriv (fun z : ℝ => φ (z - c)) y := by
    rw [← setIntegral_translate c (fun y => v y * deriv (fun z : ℝ => φ (z - c)) y) (Ioo a b),
      preimage_addRight_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun x _ => ?_
    rw [hd (x + c), add_sub_cancel_right]
  have hR : ∫ x in Ioo (a - c) (b - c), G (x + c) * φ x
      = ∫ y in Ioo a b, G y * (fun z : ℝ => φ (z - c)) y := by
    rw [← setIntegral_translate c (fun y => G y * (fun z : ℝ => φ (z - c)) y) (Ioo a b),
      preimage_addRight_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun x _ => ?_
    simp
  rw [hL, hR]
  exact key


/-! ### Deliverable 3: the absolutely continuous representative on `[ε, R]` -/

open RobinCaps.ThinDomain in
/-- For almost every direction, the radial component of an `L²` vector field has an `L¹` and an
`L²` radial slice on every `(ε, R)`. -/
theorem ae_integrableOn_slice_inner (hm : 1 ≤ m)
    (hg : MemLp g 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) R))) :
    ∀ᵐ w ∂(sphereMeasure m), ∀ ε ∈ Ioo (0 : ℝ) R,
      IntegrableOn (fun r : ℝ => inner ℝ (g (r • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
          EuclideanSpace ℝ (Fin m)))) ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
          EuclideanSpace ℝ (Fin m))) (Ioo ε R) ∧
      IntegrableOn (fun r : ℝ =>
        (inner ℝ (g (r • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
          EuclideanSpace ℝ (Fin m)))) ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
          EuclideanSpace ℝ (Fin m))) ^ 2) (Ioo ε R) := by
  haveI : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have hgint : ∀ i : Fin m, IntegrableOn (fun x => g x i)
      (ball (0 : EuclideanSpace ℝ (Fin m)) R) := fun i =>
    (memLp_two_comp hg i).integrable one_le_two
  have hgsq : IntegrableOn (fun x => ‖g x‖ ^ 2)
      (ball (0 : EuclideanSpace ℝ (Fin m)) R) := by
    refine (hg.norm.integrable_mul hg.norm).congr (Eventually.of_forall fun x => ?_)
    show ‖g x‖ * ‖g x‖ = ‖g x‖ ^ 2
    rw [pow_two]
  have h1 := ae_all_iff.2 fun i : Fin m => ae_integrableOn_slice (R := R) hm (hgint i)
  have h2 := ae_integrableOn_slice (R := R) hm hgsq
  filter_upwards [h1, h2] with w hw1 hw2 ε hε
  have hfirst : IntegrableOn (fun r : ℝ => inner ℝ (g (r • (w : EuclideanSpace ℝ (Fin m))))
      (w : EuclideanSpace ℝ (Fin m))) (Ioo ε R) := by
    have hsum : IntegrableOn (fun r : ℝ =>
        ∑ i, g (r • (w : EuclideanSpace ℝ (Fin m))) i * (w : EuclideanSpace ℝ (Fin m)) i)
        (Ioo ε R) :=
      integrable_finset_sum (μ := volume.restrict (Ioo ε R)) Finset.univ
        fun i _ => (hw1 i ε hε).mul_const _
    refine hsum.congr (Eventually.of_forall fun r => ?_)
    exact (inner_eq_sum (g (r • (w : EuclideanSpace ℝ (Fin m))))
      (w : EuclideanSpace ℝ (Fin m))).symm
  refine ⟨hfirst, ?_⟩
  have hwn : ‖(w : EuclideanSpace ℝ (Fin m))‖ = 1 := mem_sphere_zero_iff_norm.1 w.2
  refine Integrable.mono' (hw2 ε hε)
    (hfirst.aestronglyMeasurable.mul hfirst.aestronglyMeasurable |>.congr
      (Eventually.of_forall fun r => (pow_two _).symm)) ?_
  filter_upwards with r
  have hcs : |inner ℝ (g (r • (w : EuclideanSpace ℝ (Fin m))))
      (w : EuclideanSpace ℝ (Fin m))| ≤ ‖g (r • (w : EuclideanSpace ℝ (Fin m)))‖ := by
    have := abs_real_inner_le_norm (g (r • (w : EuclideanSpace ℝ (Fin m))))
      (w : EuclideanSpace ℝ (Fin m))
    rwa [hwn, mul_one] at this
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) hcs 2

open RobinCaps.ThinDomain in
/-- **Deliverable 3.**  For almost every direction `w` and every `ε ∈ (0, R)`, the radial slice
`s ↦ u ((s + ε) w)` has an absolutely continuous representative in the concrete
one-dimensional Sobolev model `RobinCaps.Sobolev.H1 (R - ε)`, whose classical derivative is the
radial component of the weak gradient. -/
theorem radialSlice_h1 (hm : 1 ≤ m) (hR : 0 < R)
    (u : H1 (ball (0 : EuclideanSpace ℝ (Fin m)) R)) :
    ∀ᵐ w ∂(sphereMeasure m), ∀ ε ∈ Ioo (0 : ℝ) R,
      ∃ W : RobinCaps.Sobolev.H1 (R - ε),
        W.toFun =ᵐ[volume.restrict (Ioo 0 (R - ε))]
          (fun s => u.toFun ((s + ε) • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
            EuclideanSpace ℝ (Fin m)))) ∧
        deriv W.toFun =ᵐ[volume.restrict (Ioo 0 (R - ε))]
          (fun s => inner ℝ (u.grad ((s + ε) • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
            EuclideanSpace ℝ (Fin m)))) ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
            EuclideanSpace ℝ (Fin m))) := by
  haveI : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have huint : IntegrableOn u.toFun (ball (0 : EuclideanSpace ℝ (Fin m)) R) :=
    u.memL2.integrable one_le_two
  filter_upwards [radialSlice_ae hm hR u, ae_integrableOn_slice (R := R) hm huint,
    ae_integrableOn_slice_inner hm u.grad_memL2] with w hw hwu hwi ε hε
  have hlen : (0 : ℝ) < R - ε := by
    have := hε.2
    linarith
  have htr := hasWeakDeriv_translate (c := ε) (hw ε hε)
  rw [sub_self] at htr
  have hv : IntegrableOn (fun s : ℝ => u.toFun ((s + ε) • (w : EuclideanSpace ℝ (Fin m))))
      (Ioo 0 (R - ε)) := by
    have := integrableOn_translate (c := ε) (hwu ε hε)
    rwa [preimage_addRight_Ioo, sub_self] at this
  have hG : IntegrableOn (fun s : ℝ => inner ℝ (u.grad ((s + ε) •
      (w : EuclideanSpace ℝ (Fin m)))) (w : EuclideanSpace ℝ (Fin m))) (Ioo 0 (R - ε)) := by
    have := integrableOn_translate (c := ε) (hwi ε hε).1
    rwa [preimage_addRight_Ioo, sub_self] at this
  have hG2 : IntegrableOn (fun s : ℝ => (inner ℝ (u.grad ((s + ε) •
      (w : EuclideanSpace ℝ (Fin m)))) (w : EuclideanSpace ℝ (Fin m))) ^ 2)
      (Ioo 0 (R - ε)) := by
    have := integrableOn_translate (c := ε) (hwi ε hε).2
    rwa [preimage_addRight_Ioo, sub_self] at this
  exact RobinCaps.Sobolev.exists_h1_of_hasWeakDeriv hlen hv hG hG2 htr


/-! ### The trace on the sphere of radius `R` -/

/-- **The sphere trace.**  The endpoint value at `r = R` of the absolutely continuous
representative of the radial slice on `[R/2, R]`, written as an explicit (choice-free) formula:
the constant of the FTC representation is recovered by averaging. -/
def traceSphere (R : ℝ) (u : EuclideanSpace ℝ (Fin m) → ℝ)
    (g : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (w : EuclideanSpace ℝ (Fin m)) : ℝ :=
  (2 / R) * (∫ r in Ioo (R / 2) R,
      (u (r • w) - ∫ t in ((R / 2 + R) / 2)..r, inner ℝ (g (t • w)) w))
    + ∫ t in ((R / 2 + R) / 2)..R, inner ℝ (g (t • w)) w

open RobinCaps.ThinDomain RobinCaps.Sobolev in
/-- **The trace of a continuous function is its restriction.**  If the representative of `u` is
continuous, then for almost every direction the sphere trace is the value of `u` on the
sphere of radius `R`. -/
theorem traceSphere_eq_of_continuous (hm : 1 ≤ m) (hR : 0 < R)
    (u : H1 (ball (0 : EuclideanSpace ℝ (Fin m)) R)) (hcont : Continuous u.toFun) :
    ∀ᵐ w ∂(sphereMeasure m),
      traceSphere R u.toFun u.grad ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
          EuclideanSpace ℝ (Fin m))
        = u.toFun (R • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
          EuclideanSpace ℝ (Fin m))) := by
  haveI : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have huint : IntegrableOn u.toFun (ball (0 : EuclideanSpace ℝ (Fin m)) R) :=
    u.memL2.integrable one_le_two
  filter_upwards [radialSlice_ae hm hR u, ae_integrableOn_slice (R := R) hm huint,
    ae_integrableOn_slice_inner hm u.grad_memL2] with w hw hwu hwi
  have hab : R / 2 < R := by linarith
  have hhalf : R / 2 ∈ Ioo (0 : ℝ) R := ⟨by linarith, hab⟩
  obtain ⟨c, hc⟩ := ae_eq_const_add_integral hab (hwu _ hhalf) (hwi _ hhalf).1 (hw _ hhalf)
  -- the averaged constant
  have hcval : (∫ r in Ioo (R / 2) R,
      (u.toFun (r • (w : EuclideanSpace ℝ (Fin m)))
        - ∫ t in ((R / 2 + R) / 2)..r,
          inner ℝ (u.grad (t • (w : EuclideanSpace ℝ (Fin m))))
            (w : EuclideanSpace ℝ (Fin m)))) = (R / 2) * c := by
    have hpt : (fun r => u.toFun (r • (w : EuclideanSpace ℝ (Fin m)))
        - ∫ t in ((R / 2 + R) / 2)..r,
          inner ℝ (u.grad (t • (w : EuclideanSpace ℝ (Fin m))))
            (w : EuclideanSpace ℝ (Fin m)))
        =ᵐ[volume.restrict (Ioo (R / 2) R)] fun _ => c := by
      filter_upwards [hc] with r hr
      rw [hr]
      ring
    rw [integral_congr_ae hpt, setIntegral_const, measureReal_def, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
    ring
  have htr : traceSphere R u.toFun u.grad (w : EuclideanSpace ℝ (Fin m))
      = c + ∫ t in ((R / 2 + R) / 2)..R,
        inner ℝ (u.grad (t • (w : EuclideanSpace ℝ (Fin m))))
          (w : EuclideanSpace ℝ (Fin m)) := by
    rw [traceSphere, hcval]
    have : (2 / R) * (R / 2 * c) = c := by field_simp
    rw [this]
  -- the continuous representative
  have hGII : IntervalIntegrable (fun t => inner ℝ (u.grad (t • (w : EuclideanSpace ℝ (Fin m))))
      (w : EuclideanSpace ℝ (Fin m))) volume (R / 2) R :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 (hwi _ hhalf).1
  have hmidmem : ((R / 2 + R) / 2) ∈ uIcc (R / 2) R := by
    rw [uIcc_of_le hab.le]
    exact ⟨by linarith, by linarith⟩
  have hPcont : ContinuousOn (fun r => ∫ t in ((R / 2 + R) / 2)..r,
      inner ℝ (u.grad (t • (w : EuclideanSpace ℝ (Fin m))))
        (w : EuclideanSpace ℝ (Fin m))) (Icc (R / 2) R) := by
    have := intervalIntegral.continuousOn_primitive_interval' hGII hmidmem
    rwa [uIcc_of_le hab.le] at this
  have hvcont : Continuous fun r : ℝ => u.toFun (r • (w : EuclideanSpace ℝ (Fin m))) :=
    hcont.comp (continuous_id.smul continuous_const)
  have hfcont : ContinuousOn (fun r : ℝ => u.toFun (r • (w : EuclideanSpace ℝ (Fin m)))
      - (c + ∫ t in ((R / 2 + R) / 2)..r,
        inner ℝ (u.grad (t • (w : EuclideanSpace ℝ (Fin m))))
          (w : EuclideanSpace ℝ (Fin m)))) (Icc (R / 2) R) :=
    hvcont.continuousOn.sub (continuousOn_const.add hPcont)
  -- the difference vanishes on the open interval
  have hkey : ∀ r ∈ Ioo (R / 2) R, u.toFun (r • (w : EuclideanSpace ℝ (Fin m)))
      - (c + ∫ t in ((R / 2 + R) / 2)..r,
        inner ℝ (u.grad (t • (w : EuclideanSpace ℝ (Fin m))))
          (w : EuclideanSpace ℝ (Fin m))) = 0 := by
    intro r hr
    by_contra hne
    have hat : ContinuousAt (fun r : ℝ => u.toFun (r • (w : EuclideanSpace ℝ (Fin m)))
        - (c + ∫ t in ((R / 2 + R) / 2)..r,
          inner ℝ (u.grad (t • (w : EuclideanSpace ℝ (Fin m))))
            (w : EuclideanSpace ℝ (Fin m)))) r :=
      hfcont.continuousAt (Icc_mem_nhds hr.1 hr.2)
    have hnb := hat.eventually (eventually_ne_nhds hne)
    have hnbd : {x : ℝ | (u.toFun (x • (w : EuclideanSpace ℝ (Fin m)))
        - (c + ∫ t in ((R / 2 + R) / 2)..x,
          inner ℝ (u.grad (t • (w : EuclideanSpace ℝ (Fin m))))
            (w : EuclideanSpace ℝ (Fin m)))) ≠ 0} ∩ Ioo (R / 2) R ∈ 𝓝 r :=
      inter_mem hnb (Ioo_mem_nhds hr.1 hr.2)
    have hpos : 0 < volume ({x : ℝ | (u.toFun (x • (w : EuclideanSpace ℝ (Fin m)))
        - (c + ∫ t in ((R / 2 + R) / 2)..x,
          inner ℝ (u.grad (t • (w : EuclideanSpace ℝ (Fin m))))
            (w : EuclideanSpace ℝ (Fin m)))) ≠ 0} ∩ Ioo (R / 2) R) :=
      MeasureTheory.Measure.measure_pos_of_mem_nhds volume hnbd
    have hnull : volume ({x : ℝ | (u.toFun (x • (w : EuclideanSpace ℝ (Fin m)))
        - (c + ∫ t in ((R / 2 + R) / 2)..x,
          inner ℝ (u.grad (t • (w : EuclideanSpace ℝ (Fin m))))
            (w : EuclideanSpace ℝ (Fin m)))) ≠ 0} ∩ Ioo (R / 2) R) = 0 := by
      have hc' : ∀ᵐ x ∂volume, x ∈ Ioo (R / 2) R →
          u.toFun (x • (w : EuclideanSpace ℝ (Fin m)))
            = c + ∫ t in ((R / 2 + R) / 2)..x,
              inner ℝ (u.grad (t • (w : EuclideanSpace ℝ (Fin m))))
                (w : EuclideanSpace ℝ (Fin m)) :=
        (ae_restrict_iff' measurableSet_Ioo).1 hc
      refine measure_mono_null (fun x hx => ?_) hc'
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff] at hx ⊢
      intro hcon
      exact hx.1 (by rw [hcon hx.2]; ring)
    rw [hnull] at hpos
    exact lt_irrefl 0 hpos
  -- pass to the endpoint
  have hfR : u.toFun (R • (w : EuclideanSpace ℝ (Fin m)))
      - (c + ∫ t in ((R / 2 + R) / 2)..R,
        inner ℝ (u.grad (t • (w : EuclideanSpace ℝ (Fin m))))
          (w : EuclideanSpace ℝ (Fin m))) = 0 := by
    haveI hnebot : (𝓝[Ioo (R / 2) R] R).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo (ne_of_lt hab)]
      exact right_mem_Icc.2 hab.le
    have h1 := (hfcont R (right_mem_Icc.2 hab.le)).mono_left
      (nhdsWithin_mono R Ioo_subset_Icc_self)
    have h2 : Tendsto (fun r : ℝ => u.toFun (r • (w : EuclideanSpace ℝ (Fin m)))
        - (c + ∫ t in ((R / 2 + R) / 2)..r,
          inner ℝ (u.grad (t • (w : EuclideanSpace ℝ (Fin m))))
            (w : EuclideanSpace ℝ (Fin m)))) (𝓝[Ioo (R / 2) R] R) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r hr using (hkey r hr).symm
    exact tendsto_nhds_unique h1 h2
  rw [htr]
  linarith [hfR]


/-! ### The radial one-dimensional trace bound -/

/-- Two functions continuous on `[a,b]` and almost everywhere equal on `(a,b)` take the same
value at the right endpoint. -/
theorem eq_of_ae_eq_of_continuousOn {a b : ℝ} (hab : a < b) {f₁ f₂ : ℝ → ℝ}
    (h1 : ContinuousOn f₁ (Icc a b)) (h2 : ContinuousOn f₂ (Icc a b))
    (hae : f₁ =ᵐ[volume.restrict (Ioo a b)] f₂) : f₁ b = f₂ b := by
  have hfcont : ContinuousOn (fun r => f₁ r - f₂ r) (Icc a b) := h1.sub h2
  have hkey : ∀ r ∈ Ioo a b, f₁ r - f₂ r = 0 := by
    intro r hr
    by_contra hne
    have hat : ContinuousAt (fun r => f₁ r - f₂ r) r :=
      hfcont.continuousAt (Icc_mem_nhds hr.1 hr.2)
    have hnb := hat.eventually (eventually_ne_nhds hne)
    have hnbd : {x : ℝ | f₁ x - f₂ x ≠ 0} ∩ Ioo a b ∈ 𝓝 r :=
      inter_mem hnb (Ioo_mem_nhds hr.1 hr.2)
    have hpos : 0 < volume ({x : ℝ | f₁ x - f₂ x ≠ 0} ∩ Ioo a b) :=
      MeasureTheory.Measure.measure_pos_of_mem_nhds volume hnbd
    have hnull : volume ({x : ℝ | f₁ x - f₂ x ≠ 0} ∩ Ioo a b) = 0 := by
      have hae' : ∀ᵐ x ∂volume, x ∈ Ioo a b → f₁ x = f₂ x :=
        (ae_restrict_iff' measurableSet_Ioo).1 hae
      refine measure_mono_null (fun x hx => ?_) hae'
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff] at hx ⊢
      intro hcon
      exact hx.1 (by rw [hcon hx.2]; ring)
    rw [hnull] at hpos
    exact lt_irrefl 0 hpos
  have hnebot : (𝓝[Ioo a b] b).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo (ne_of_lt hab)]
    exact right_mem_Icc.2 hab.le
  have hlim1 := (hfcont b (right_mem_Icc.2 hab.le)).mono_left
    (nhdsWithin_mono b Ioo_subset_Icc_self)
  have hlim2 : Tendsto (fun r => f₁ r - f₂ r) (𝓝[Ioo a b] b) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr using (hkey r hr).symm
  have := tendsto_nhds_unique hlim1 hlim2
  linarith [this]

/-- Almost-everywhere equality is preserved by translation. -/
theorem ae_eq_translate {c : ℝ} {s : Set ℝ} {f₁ f₂ : ℝ → ℝ}
    (h : f₁ =ᵐ[volume.restrict s] f₂) :
    (fun x => f₁ (x + c)) =ᵐ[volume.restrict ((fun x : ℝ => x + c) ⁻¹' s)]
      (fun x => f₂ (x + c)) :=
  (((measurePreserving_addRight' c).restrict_preimage_emb
    (measurableEmbedding_addRight' c) s).quasiMeasurePreserving).ae_eq_comp h

open RobinCaps.ThinDomain RobinCaps.Sobolev in
/-- The representation of the sphere trace as the endpoint value of the FTC representative of
the radial slice on `(R/2, R)`. -/
theorem traceSphere_eq_const_add (hm : 1 ≤ m) (hR : 0 < R)
    (u : H1 (ball (0 : EuclideanSpace ℝ (Fin m)) R)) :
    ∀ᵐ w ∂(sphereMeasure m), ∃ c : ℝ,
      (fun r => u.toFun (r • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
          EuclideanSpace ℝ (Fin m))))
        =ᵐ[volume.restrict (Ioo (R / 2) R)]
        (fun r => c + ∫ t in ((R / 2 + R) / 2)..r,
          inner ℝ (u.grad (t • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
            EuclideanSpace ℝ (Fin m)))) ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
            EuclideanSpace ℝ (Fin m))) ∧
      traceSphere R u.toFun u.grad ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
          EuclideanSpace ℝ (Fin m))
        = c + ∫ t in ((R / 2 + R) / 2)..R,
          inner ℝ (u.grad (t • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
            EuclideanSpace ℝ (Fin m)))) ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
            EuclideanSpace ℝ (Fin m)) := by
  haveI : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have huint : IntegrableOn u.toFun (ball (0 : EuclideanSpace ℝ (Fin m)) R) :=
    u.memL2.integrable one_le_two
  filter_upwards [radialSlice_ae hm hR u, ae_integrableOn_slice (R := R) hm huint,
    ae_integrableOn_slice_inner hm u.grad_memL2] with w hw hwu hwi
  have hab : R / 2 < R := by linarith
  have hhalf : R / 2 ∈ Ioo (0 : ℝ) R := ⟨by linarith, hab⟩
  obtain ⟨c, hc⟩ := ae_eq_const_add_integral hab (hwu _ hhalf) (hwi _ hhalf).1 (hw _ hhalf)
  refine ⟨c, hc, ?_⟩
  have hcval : (∫ r in Ioo (R / 2) R,
      (u.toFun (r • (w : EuclideanSpace ℝ (Fin m)))
        - ∫ t in ((R / 2 + R) / 2)..r,
          inner ℝ (u.grad (t • (w : EuclideanSpace ℝ (Fin m))))
            (w : EuclideanSpace ℝ (Fin m)))) = (R / 2) * c := by
    have hpt : (fun r => u.toFun (r • (w : EuclideanSpace ℝ (Fin m)))
        - ∫ t in ((R / 2 + R) / 2)..r,
          inner ℝ (u.grad (t • (w : EuclideanSpace ℝ (Fin m))))
            (w : EuclideanSpace ℝ (Fin m)))
        =ᵐ[volume.restrict (Ioo (R / 2) R)] fun _ => c := by
      filter_upwards [hc] with r hr
      rw [hr]
      ring
    rw [integral_congr_ae hpt, setIntegral_const, measureReal_def, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
    ring
  rw [traceSphere, hcval]
  have h2 : (2 / R) * (R / 2 * c) = c := by field_simp
  rw [h2]

open RobinCaps.ThinDomain RobinCaps.Sobolev in
/-- **The radial one-dimensional trace bound.**  For almost every direction,
`|Tr u (w)|² ≤ (4/R) ∫_{R/2}^R |u(r w)|² dr + R ∫_{R/2}^R |⟪∇u(r w), w⟫|² dr`. -/
theorem traceSphere_sq_le (hm : 1 ≤ m) (hR : 0 < R)
    (u : H1 (ball (0 : EuclideanSpace ℝ (Fin m)) R)) :
    ∀ᵐ w ∂(sphereMeasure m),
      (traceSphere R u.toFun u.grad ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
        EuclideanSpace ℝ (Fin m))) ^ 2
        ≤ (4 / R) * (∫ r in Ioo (R / 2) R,
            (u.toFun (r • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
              EuclideanSpace ℝ (Fin m)))) ^ 2)
          + R * ∫ r in Ioo (R / 2) R,
            (inner ℝ (u.grad (r • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
              EuclideanSpace ℝ (Fin m)))) ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
              EuclideanSpace ℝ (Fin m))) ^ 2 := by
  haveI : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have huint : IntegrableOn u.toFun (ball (0 : EuclideanSpace ℝ (Fin m)) R) :=
    u.memL2.integrable one_le_two
  filter_upwards [traceSphere_eq_const_add hm hR u, radialSlice_h1 hm hR u,
    ae_integrableOn_slice_inner (R := R) hm u.grad_memL2] with w hchar hW hwi
  obtain ⟨c, hc, htr⟩ := hchar
  have hab : R / 2 < R := by linarith
  have hhalf : R / 2 ∈ Ioo (0 : ℝ) R := ⟨by linarith, hab⟩
  have hlen : (0 : ℝ) < R - R / 2 := by linarith
  obtain ⟨W, hW1, hW2⟩ := hW (R / 2) hhalf
  -- the endpoint of the concrete representative is the trace
  have hGII : IntervalIntegrable (fun t => inner ℝ (u.grad (t • (w : EuclideanSpace ℝ (Fin m))))
      (w : EuclideanSpace ℝ (Fin m))) volume (R / 2) R :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 (hwi _ hhalf).1
  have hPcont : ContinuousOn (fun r => ∫ t in ((R / 2 + R) / 2)..r,
      inner ℝ (u.grad (t • (w : EuclideanSpace ℝ (Fin m))))
        (w : EuclideanSpace ℝ (Fin m))) (Icc (R / 2) R) := by
    have hmidmem : ((R / 2 + R) / 2) ∈ uIcc (R / 2) R := by
      rw [uIcc_of_le hab.le]
      exact ⟨by linarith, by linarith⟩
    have := intervalIntegral.continuousOn_primitive_interval' hGII hmidmem
    rwa [uIcc_of_le hab.le] at this
  have hWae : W.toFun =ᵐ[volume.restrict (Ioo 0 (R - R / 2))]
      fun s => c + ∫ t in ((R / 2 + R) / 2)..(s + R / 2),
        inner ℝ (u.grad (t • (w : EuclideanSpace ℝ (Fin m))))
          (w : EuclideanSpace ℝ (Fin m)) := by
    have htrans := ae_eq_translate (c := R / 2) hc
    rw [preimage_addRight_Ioo, sub_self] at htrans
    exact hW1.trans htrans
  have hWcont : ContinuousOn W.toFun (Icc 0 (R - R / 2)) := by
    have h := W.ac.continuousOn
    rwa [uIcc_of_le hlen.le] at h
  have hRcont : ContinuousOn (fun s => c + ∫ t in ((R / 2 + R) / 2)..(s + R / 2),
      inner ℝ (u.grad (t • (w : EuclideanSpace ℝ (Fin m))))
        (w : EuclideanSpace ℝ (Fin m))) (Icc 0 (R - R / 2)) := by
    refine continuousOn_const.add (ContinuousOn.comp hPcont
      (Continuous.continuousOn (continuous_id.add continuous_const)) ?_)
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hWend : W.toFun (R - R / 2)
      = c + ∫ t in ((R / 2 + R) / 2)..R,
        inner ℝ (u.grad (t • (w : EuclideanSpace ℝ (Fin m))))
          (w : EuclideanSpace ℝ (Fin m)) := by
    have := eq_of_ae_eq_of_continuousOn hlen hWcont hRcont hWae
    rw [this]
    norm_num
  -- the mass and the Dirichlet energy of the representative
  have hmass : RobinCaps.Sobolev.mass (R - R / 2) W
      = ∫ r in Ioo (R / 2) R, (u.toFun (r • (w : EuclideanSpace ℝ (Fin m)))) ^ 2 := by
    rw [RobinCaps.Sobolev.mass, intervalIntegral_eq_setIntegral_Ioo hlen.le]
    have h1 : (fun x => W.toFun x ^ 2)
        =ᵐ[volume.restrict (Ioo 0 (R - R / 2))]
        fun x => (u.toFun ((x + R / 2) • (w : EuclideanSpace ℝ (Fin m)))) ^ 2 := by
      filter_upwards [hW1] with x hx
      rw [hx]
    rw [integral_congr_ae h1]
    have h2 := setIntegral_translate (R / 2)
      (fun y => (u.toFun (y • (w : EuclideanSpace ℝ (Fin m)))) ^ 2) (Ioo (R / 2) R)
    rw [preimage_addRight_Ioo, sub_self] at h2
    exact h2
  have hdir : RobinCaps.Sobolev.dirichlet (R - R / 2) W
      = ∫ r in Ioo (R / 2) R, (inner ℝ (u.grad (r • (w : EuclideanSpace ℝ (Fin m))))
        (w : EuclideanSpace ℝ (Fin m))) ^ 2 := by
    rw [RobinCaps.Sobolev.dirichlet, intervalIntegral_eq_setIntegral_Ioo hlen.le]
    have h1 : (fun x => deriv W.toFun x ^ 2)
        =ᵐ[volume.restrict (Ioo 0 (R - R / 2))]
        fun x => (inner ℝ (u.grad ((x + R / 2) • (w : EuclideanSpace ℝ (Fin m))))
          (w : EuclideanSpace ℝ (Fin m))) ^ 2 := by
      filter_upwards [hW2] with x hx
      rw [hx]
    rw [integral_congr_ae h1]
    have h2 := setIntegral_translate (R / 2)
      (fun y => (inner ℝ (u.grad (y • (w : EuclideanSpace ℝ (Fin m))))
        (w : EuclideanSpace ℝ (Fin m))) ^ 2) (Ioo (R / 2) R)
    rw [preimage_addRight_Ioo, sub_self] at h2
    exact h2
  have hbound := RobinCaps.Sobolev.endpoint_ell_sq_le W hlen
  rw [hmass, hdir] at hbound
  rw [htr, ← hWend]
  have h4 : 2 / (R - R / 2) = 4 / R := by
    rw [show R - R / 2 = R / 2 by ring]
    field_simp
    norm_num
  have h5 : 2 * (R - R / 2) = R := by ring
  rw [h4, h5] at hbound
  exact hbound


/-! ### Deliverable 4: the trace inequality on the sphere of radius `R` -/

open RobinCaps.ThinDomain in
/-- The weighted radial slice of a function integrable on the ball is integrable on `(0,R)`. -/
theorem ae_integrableOn_weighted (hm : 1 ≤ m) {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf : IntegrableOn f (ball (0 : EuclideanSpace ℝ (Fin m)) R)) :
    ∀ᵐ w ∂(sphereMeasure m), IntegrableOn
      (fun r : ℝ => r ^ (m - 1) * f (r • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
        EuclideanSpace ℝ (Fin m)))) (Ioo (0 : ℝ) R) := by
  filter_upwards [ae_integrableOn_radialSlice (R := R) hm hf] with w hw
  have h1 : IntegrableOn (fun r : ℝ => r ^ (m - 1) *
      (ball (0 : EuclideanSpace ℝ (Fin m)) R).indicator f
        (r • (w : EuclideanSpace ℝ (Fin m)))) (Ioo (0 : ℝ) R) :=
    hw.mono_set Ioo_subset_Ioi_self
  refine h1.congr_fun (fun r hr => ?_) measurableSet_Ioo
  have hr0 : (0 : ℝ) < r := hr.1
  rw [Set.indicator_of_mem
    (by simpa [mem_ball_zero_iff, norm_smul_sphere hr0 w] using hr.2)]

open RobinCaps.ThinDomain RobinCaps.Sobolev in
/-- **Deliverable 4: the trace inequality on the sphere of radius `R`.**
`∫_{S} |Tr u|² dσ ≤ C(R,m) (‖u‖²_{L²(B)} + ‖∇u‖²_{L²(B)})`. -/
theorem traceSphere_sq_integral_le (hm : 1 ≤ m) (hR : 0 < R)
    (u : H1 (ball (0 : EuclideanSpace ℝ (Fin m)) R)) :
    (∫ w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        (traceSphere R u.toFun u.grad (w : EuclideanSpace ℝ (Fin m))) ^ 2 ∂(sphereMeasure m))
      ≤ max ((4 / R) * (((R / 2) ^ (m - 1))⁻¹)) (R * (((R / 2) ^ (m - 1))⁻¹))
        * (mass u + dirichlet u) := by
  haveI : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have hhalfpos : (0 : ℝ) < R / 2 := by linarith
  have hKpos : (0 : ℝ) < ((R / 2) ^ (m - 1))⁻¹ := by positivity
  -- the two `L¹` data on the ball
  have hu2 : IntegrableOn (fun x => u.toFun x ^ 2)
      (ball (0 : EuclideanSpace ℝ (Fin m)) R) := by
    refine (u.memL2.integrable_mul u.memL2).congr (Eventually.of_forall fun x => ?_)
    show u.toFun x * u.toFun x = u.toFun x ^ 2
    rw [pow_two]
  have hg2 : IntegrableOn (fun x => ‖u.grad x‖ ^ 2)
      (ball (0 : EuclideanSpace ℝ (Fin m)) R) := by
    refine (u.grad_memL2.norm.integrable_mul u.grad_memL2.norm).congr
      (Eventually.of_forall fun x => ?_)
    show ‖u.grad x‖ * ‖u.grad x‖ = ‖u.grad x‖ ^ 2
    rw [pow_two]
  -- the integrable majorant on the sphere
  have hB1 := integrable_ball_angular hm hu2
  have hB2 := integrable_ball_angular hm hg2
  have hN : Integrable (fun w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      (4 / R) * ((R / 2) ^ (m - 1))⁻¹ * (∫ r in Ioo (0 : ℝ) R,
          r ^ (m - 1) * (u.toFun (r • (w : EuclideanSpace ℝ (Fin m)))) ^ 2)
        + R * ((R / 2) ^ (m - 1))⁻¹ * ∫ r in Ioo (0 : ℝ) R,
          r ^ (m - 1) * ‖u.grad (r • (w : EuclideanSpace ℝ (Fin m)))‖ ^ 2) (sphereMeasure m) :=
    (hB1.const_mul _).add (hB2.const_mul _)
  -- the pointwise bound
  have hptwise : ∀ᵐ w ∂(sphereMeasure m),
      (traceSphere R u.toFun u.grad ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
        EuclideanSpace ℝ (Fin m))) ^ 2
      ≤ (4 / R) * ((R / 2) ^ (m - 1))⁻¹ * (∫ r in Ioo (0 : ℝ) R,
          r ^ (m - 1) * (u.toFun (r • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
            EuclideanSpace ℝ (Fin m)))) ^ 2)
        + R * ((R / 2) ^ (m - 1))⁻¹ * ∫ r in Ioo (0 : ℝ) R,
          r ^ (m - 1) * ‖u.grad (r • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
            EuclideanSpace ℝ (Fin m)))‖ ^ 2 := by
    filter_upwards [traceSphere_sq_le hm hR u, ae_integrableOn_weighted (R := R) hm hu2,
      ae_integrableOn_weighted (R := R) hm hg2] with w htr h2 h3
    have hsub : Ioo (R / 2) R ⊆ Ioo (0 : ℝ) R := Ioo_subset_Ioo (by linarith) le_rfl
    have hweight : ∀ r ∈ Ioo (R / 2) R, (1 : ℝ) ≤ ((R / 2) ^ (m - 1))⁻¹ * r ^ (m - 1) := by
      intro r hr
      have hp : (0 : ℝ) < (R / 2) ^ (m - 1) := by positivity
      have h1 : (R / 2) ^ (m - 1) ≤ r ^ (m - 1) := by
        gcongr
        exact hr.1.le
      rw [inv_mul_eq_div, le_div_iff₀ hp, one_mul]
      exact h1
    -- first term
    have hA1 : (∫ r in Ioo (R / 2) R, (u.toFun (r • (w : EuclideanSpace ℝ (Fin m)))) ^ 2)
        ≤ ((R / 2) ^ (m - 1))⁻¹ * ∫ r in Ioo (0 : ℝ) R,
          r ^ (m - 1) * (u.toFun (r • (w : EuclideanSpace ℝ (Fin m)))) ^ 2 := by
      have hmaj : IntegrableOn (fun r : ℝ => ((R / 2) ^ (m - 1))⁻¹ *
          (r ^ (m - 1) * (u.toFun (r • (w : EuclideanSpace ℝ (Fin m)))) ^ 2))
          (Ioo (R / 2) R) := (h2.mono_set hsub).const_mul _
      have step1 : (∫ r in Ioo (R / 2) R, (u.toFun (r • (w : EuclideanSpace ℝ (Fin m)))) ^ 2)
          ≤ ∫ r in Ioo (R / 2) R, ((R / 2) ^ (m - 1))⁻¹ *
            (r ^ (m - 1) * (u.toFun (r • (w : EuclideanSpace ℝ (Fin m)))) ^ 2) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun r => sq_nonneg _) hmaj ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
        have hwt := hweight r hr
        calc (u.toFun (r • (w : EuclideanSpace ℝ (Fin m)))) ^ 2
            = 1 * (u.toFun (r • (w : EuclideanSpace ℝ (Fin m)))) ^ 2 := (one_mul _).symm
          _ ≤ (((R / 2) ^ (m - 1))⁻¹ * r ^ (m - 1))
              * (u.toFun (r • (w : EuclideanSpace ℝ (Fin m)))) ^ 2 :=
            mul_le_mul_of_nonneg_right hwt (sq_nonneg _)
          _ = ((R / 2) ^ (m - 1))⁻¹
              * (r ^ (m - 1) * (u.toFun (r • (w : EuclideanSpace ℝ (Fin m)))) ^ 2) := by ring
      have step2 : (∫ r in Ioo (R / 2) R, ((R / 2) ^ (m - 1))⁻¹ *
            (r ^ (m - 1) * (u.toFun (r • (w : EuclideanSpace ℝ (Fin m)))) ^ 2))
          ≤ ((R / 2) ^ (m - 1))⁻¹ * ∫ r in Ioo (0 : ℝ) R,
            (r ^ (m - 1) * (u.toFun (r • (w : EuclideanSpace ℝ (Fin m)))) ^ 2) := by
        rw [← integral_const_mul]
        refine setIntegral_mono_set (h2.const_mul _) ?_ (HasSubset.Subset.eventuallyLE hsub)
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
        have hr0 : (0 : ℝ) < r := hr.1
        positivity
      linarith
    -- second term
    have hA2 : (∫ r in Ioo (R / 2) R,
          (inner ℝ (u.grad (r • (w : EuclideanSpace ℝ (Fin m))))
            (w : EuclideanSpace ℝ (Fin m))) ^ 2)
        ≤ ((R / 2) ^ (m - 1))⁻¹ * ∫ r in Ioo (0 : ℝ) R,
          r ^ (m - 1) * ‖u.grad (r • (w : EuclideanSpace ℝ (Fin m)))‖ ^ 2 := by
      have hwn : ‖(w : EuclideanSpace ℝ (Fin m))‖ = 1 := mem_sphere_zero_iff_norm.1 w.2
      have hmaj : IntegrableOn (fun r : ℝ => ((R / 2) ^ (m - 1))⁻¹ *
          (r ^ (m - 1) * ‖u.grad (r • (w : EuclideanSpace ℝ (Fin m)))‖ ^ 2))
          (Ioo (R / 2) R) := (h3.mono_set hsub).const_mul _
      have step1 : (∫ r in Ioo (R / 2) R,
            (inner ℝ (u.grad (r • (w : EuclideanSpace ℝ (Fin m))))
              (w : EuclideanSpace ℝ (Fin m))) ^ 2)
          ≤ ∫ r in Ioo (R / 2) R, ((R / 2) ^ (m - 1))⁻¹ *
            (r ^ (m - 1) * ‖u.grad (r • (w : EuclideanSpace ℝ (Fin m)))‖ ^ 2) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun r => sq_nonneg _) hmaj ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
        have hcs : |inner ℝ (u.grad (r • (w : EuclideanSpace ℝ (Fin m))))
            (w : EuclideanSpace ℝ (Fin m))| ≤ ‖u.grad (r • (w : EuclideanSpace ℝ (Fin m)))‖ := by
          have := abs_real_inner_le_norm (u.grad (r • (w : EuclideanSpace ℝ (Fin m))))
            (w : EuclideanSpace ℝ (Fin m))
          rwa [hwn, mul_one] at this
        have hsq : (inner ℝ (u.grad (r • (w : EuclideanSpace ℝ (Fin m))))
            (w : EuclideanSpace ℝ (Fin m))) ^ 2
            ≤ ‖u.grad (r • (w : EuclideanSpace ℝ (Fin m)))‖ ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hcs 2
        have hwt := hweight r hr
        calc (inner ℝ (u.grad (r • (w : EuclideanSpace ℝ (Fin m))))
                (w : EuclideanSpace ℝ (Fin m))) ^ 2
            ≤ ‖u.grad (r • (w : EuclideanSpace ℝ (Fin m)))‖ ^ 2 := hsq
          _ = 1 * ‖u.grad (r • (w : EuclideanSpace ℝ (Fin m)))‖ ^ 2 := (one_mul _).symm
          _ ≤ (((R / 2) ^ (m - 1))⁻¹ * r ^ (m - 1))
              * ‖u.grad (r • (w : EuclideanSpace ℝ (Fin m)))‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hwt (sq_nonneg _)
          _ = ((R / 2) ^ (m - 1))⁻¹
              * (r ^ (m - 1) * ‖u.grad (r • (w : EuclideanSpace ℝ (Fin m)))‖ ^ 2) := by ring
      have step2 : (∫ r in Ioo (R / 2) R, ((R / 2) ^ (m - 1))⁻¹ *
            (r ^ (m - 1) * ‖u.grad (r • (w : EuclideanSpace ℝ (Fin m)))‖ ^ 2))
          ≤ ((R / 2) ^ (m - 1))⁻¹ * ∫ r in Ioo (0 : ℝ) R,
            (r ^ (m - 1) * ‖u.grad (r • (w : EuclideanSpace ℝ (Fin m)))‖ ^ 2) := by
        rw [← integral_const_mul]
        refine setIntegral_mono_set (h3.const_mul _) ?_ (HasSubset.Subset.eventuallyLE hsub)
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
        have hr0 : (0 : ℝ) < r := hr.1
        positivity
      linarith
    have h4R : (0 : ℝ) < 4 / R := by positivity
    nlinarith [htr, hA1, hA2, hR.le]
  -- integrate over the sphere
  have hmono := integral_mono_of_nonneg
    (Eventually.of_forall fun w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 => sq_nonneg
      (traceSphere R u.toFun u.grad (w : EuclideanSpace ℝ (Fin m)))) hN hptwise
  have hsplit : (∫ w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        ((4 / R) * ((R / 2) ^ (m - 1))⁻¹ * (∫ r in Ioo (0 : ℝ) R,
            r ^ (m - 1) * (u.toFun (r • (w : EuclideanSpace ℝ (Fin m)))) ^ 2)
          + R * ((R / 2) ^ (m - 1))⁻¹ * ∫ r in Ioo (0 : ℝ) R,
            r ^ (m - 1) * ‖u.grad (r • (w : EuclideanSpace ℝ (Fin m)))‖ ^ 2)
        ∂(sphereMeasure m))
      = (4 / R) * ((R / 2) ^ (m - 1))⁻¹ * mass u
        + R * ((R / 2) ^ (m - 1))⁻¹ * dirichlet u := by
    rw [integral_add (hB1.const_mul _) (hB2.const_mul _), integral_const_mul, integral_const_mul,
      ← integral_ball_polar_symm hm hu2, ← integral_ball_polar_symm hm hg2]
    rfl
  rw [hsplit] at hmono
  have hm0 : 0 ≤ mass u := mass_nonneg u
  have hd0 : 0 ≤ dirichlet u := dirichlet_nonneg u
  have hle1 : (4 / R) * ((R / 2) ^ (m - 1))⁻¹
      ≤ max ((4 / R) * (((R / 2) ^ (m - 1))⁻¹)) (R * (((R / 2) ^ (m - 1))⁻¹)) := le_max_left _ _
  have hle2 : R * ((R / 2) ^ (m - 1))⁻¹
      ≤ max ((4 / R) * (((R / 2) ^ (m - 1))⁻¹)) (R * (((R / 2) ^ (m - 1))⁻¹)) := le_max_right _ _
  nlinarith [hmono, mul_le_mul_of_nonneg_right hle1 hm0, mul_le_mul_of_nonneg_right hle2 hd0]


/-! ### Axiom audit -/


end

end RobinCaps.Sobolev.Weak
