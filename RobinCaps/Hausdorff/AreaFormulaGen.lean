import Mathlib
import RobinCaps.Hausdorff.AreaFormulaInj
import RobinCaps.Hausdorff.LinearImage

/-!
# The general area formula, without injectivity of the derivative (wave 12, A4 step)

This file proves `areaFormulaGen_agg`, the statement `AreaFormulaGenProp m k` from
`RobinCaps.Hausdorff.BoundaryIface`: the area formula
`μH[m] (F '' S) = ∫⁻ x in S, √(gramDet (F' x)) ∂μH[m]`
for a measurable `S ⊆ E_m := EuclideanSpace ℝ (Fin m)`, a map `F : E_m → E_k`
(`E_k := EuclideanSpace ℝ (Fin k)`) with `HasFDerivWithinAt F (F' x) S x` at every `x ∈ S`, and
`F` injective on `S` -- crucially, *without* assuming `F' x` injective anywhere. This upgrades
`RobinCaps.Hausdorff.AreaFormulaInj.areaFormulaInj_agi` (which assumes `F' x` injective at every
`x ∈ S`, and is itself proved unconditionally) to the full generality of the area formula.

## Strategy

Write `Z := {x ∈ S | ¬ Function.Injective (F' x)}` for the *critical set* and `S⁺ := S \ Z`. Since
`gramDet A = det (A† A) ≥ 0` always (`A† A` is positive semi-definite,
`ContinuousLinearMap.isPositive_adjoint_comp_self`), and `A` is injective iff `A† A` is injective
iff `det (A† A) ≠ 0` (`LinearMap.det_eq_zero_iff_ker_ne_bot`), we get
`gramDet_pos_iff_injective_agg : 0 < gramDet A ↔ Function.Injective A`, so
`Z = S ∩ {x | gramDet (F' x) = 0}` and `F' x` is injective at every `x ∈ S⁺`.

* **Main part (`S⁺`).** `areaFormulaInj_agi` applies directly to `S⁺`, giving
  `μH[m] (F '' S⁺) = ∫⁻_{S⁺} √gramDet`. The subtlety is that `F'` is only defined pointwise (no
  continuity), so `S⁺` need not literally be measurable. We sidestep this: `F'` is
  `AEMeasurable` on `S` (`aemeasurableFderivWithin_agg`, transcribing mathlib's
  `aemeasurable_fderivWithin` via the codomain-generalized density-point estimate
  `approxLinearOnNormFderivWithinSubLe_agi` from `AreaFormulaInj.lean`), so there is a measurable
  representative `G` and a *measurable, genuinely null* set `Bad ⊇ {x ∈ S | F' x ≠ G x}`
  (`MeasureTheory.exists_measurable_superset_of_null`). Away from `Bad`, `F' = G` **exactly**
  (not just a.e.), so `S⁺'' := (S \ Bad) ∩ {x | gramDet (G x) ≠ 0}` is a genuinely measurable set
  that is *pointwise* contained in `S⁺` (`criticalSetFull_agg`/`areaFormulaGen_agg`), hence
  `areaFormulaInj_agi` applies to it directly, losing nothing but the null set `S ∩ Bad` and the
  genuinely degenerate part `Z₀ := (S \ Bad) ∩ {x | gramDet (F' x) = 0}`.

* **Degenerate part (`Z₀`, Sard-type argument).** The heart of the file:
  `criticalSetPiece_image_zero_agg` shows `μH[m] (F '' N) = 0` for any measurable, bounded
  (`N ⊆ closedBall 0 M`) piece of `Z₀` on which `‖F' ·‖ ≤ M`. The idea (a one-dimension-higher
  regularization of Sard's theorem) is to lift `F` to
  `F_δ x := (F x, δ • x) : E_m → E_k × E_m` (realized concretely as `Fmap_agg δ F : E_m → E_{k+m}`
  via the L²-product `WithLp 2 (E_k × E_m)` and an isometry `eLift_agg k m` to
  `EuclideanSpace ℝ (Fin (k+m))`, built from `OrthonormalBasis.prod` exactly as the isometries in
  `LinearImage.lean`). Since `Fmap_agg`'s derivative always has an *injective* second ("`δ • id`")
  block, `Fmap_agg`'s derivative is injective everywhere and `Fmap_agg` itself is injective
  (from that same block, regardless of `F`), so `areaFormulaInj_agi` applies unconditionally to
  `Fmap_agg δ F` on all of `N`. The Gram determinant of the lifted derivative is computed exactly,
  `gramDet (Fmap_agg'x) = det (F'x† F'x + δ² • id)` (`gramDet_FmapDeriv_eq_agg`,
  `Hmap_adjoint_comp_agg`, via the L²-product inner-product formula `WithLp.prod_inner_apply`).
  On `N`, `F'x† F'x` is self-adjoint, positive semi-definite, and singular
  (`gramDet (F' x) = 0`); diagonalizing it in an eigenbasis (`LinearMap.IsSymmetric.eigenvectorBasis`,
  packaged as `detOfDiag_agg`) exhibits a zero eigenvalue, giving the bound
  `det (F'x† F'x + δ² • id) ≤ δ² (‖F'x‖² + δ²)^(m-1)` (`gramDetShift_bound_agg`), uniformly small
  as `δ → 0` on the bounded piece `N`. Projecting back to `E_k` via the 1-Lipschitz first-block
  projection `projLift_agg k m` (`WithLp.norm_fst_le`,
  `LipschitzWith.hausdorffMeasure_image_le`) transfers this bound to `μH[m] (F '' N)`, which is
  therefore `≤ 0` for every `δ > 0`, hence `= 0`. Exhausting `Z₀` by the bounded pieces
  `N_M := Z₀ ∩ {‖G ·‖ ≤ M} ∩ closedBall 0 M` and using countable subadditivity gives
  `μH[m] (F '' Z₀) = 0` (`criticalSetFull_agg`).

* **A genuinely null (not necessarily bounded) measurable set has null image regardless of
  injectivity of the derivative** (`nullSetImage_agg`): the same lift/projection argument, applied
  directly to the whole null set with a fixed `δ = 1` (no limit needed, since the domain integral
  of *any* function over a null set vanishes, `setLIntegral_measure_zero`), bounds the image of
  `S ∩ Bad`.

* **Combination.** `S = S⁺'' ⊔ (S ∩ Bad) ⊔ Z₀` (a disjoint, measurable-away-from-`S⁺''`
  decomposition); the image measure and the domain integral are both computed on `S⁺''` by
  `areaFormulaInj_agi`, and both receive a zero contribution from the other two pieces (the image
  measure by `nullSetImage_agg`/`criticalSetFull_agg`, the integral because it vanishes outright
  on a null set and is pointwise zero on `Z₀`), giving the formula on all of `S`.

No hypothesis is left open: `areaFormulaGen_agg` is proved unconditionally, ultimately from
`areaFormulaInj_agi` (itself unconditional) and the general-purpose mathlib facts cited above.
-/

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter Metric Module Function
open scoped ENNReal NNReal Topology Pointwise

namespace RobinCaps.Hausdorff

variable {m k : ℕ}

/-- The L²-product realization of the codomain `E_k × E_m` of the lift `Fmap_agg`. -/
abbrev Plift_agg (k m : ℕ) : Type := WithLp 2 (Esp_har k × Esp_har m)

def eLift_agg (k m : ℕ) : Plift_agg k m ≃ₗᵢ[ℝ] Esp_har (k + m) :=
  ((((stdOrthonormalBasis ℝ (Esp_har k)).reindex (finCongr finrank_euclideanSpace_fin)).prod
    ((stdOrthonormalBasis ℝ (Esp_har m)).reindex (finCongr finrank_euclideanSpace_fin))).reindex
    finSumFinEquiv).repr

def Hmap_agg (A : Esp_har m →L[ℝ] Esp_har k) (δ : ℝ) : Esp_har m →L[ℝ] Plift_agg k m :=
  (WithLp.linearEquiv 2 ℝ (Esp_har k × Esp_har m)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (A.prod (δ • ContinuousLinearMap.id ℝ (Esp_har m)))

theorem Hmap_apply_agg (A : Esp_har m →L[ℝ] Esp_har k) (δ : ℝ) (v : Esp_har m) :
    Hmap_agg A δ v = (WithLp.toLp 2 (A v, δ • v) : Plift_agg k m) := rfl

def Fmap_agg (δ : ℝ) (F : Esp_har m → Esp_har k) (x : Esp_har m) : Esp_har (k + m) :=
  (eLift_agg k m) (WithLp.toLp 2 (F x, δ • x))

def FmapDeriv_agg (F' : Esp_har m →L[ℝ] Esp_har k) (δ : ℝ) : Esp_har m →L[ℝ] Esp_har (k + m) :=
  (eLift_agg k m).toContinuousLinearMap.comp (Hmap_agg F' δ)

theorem hasFDerivWithinAt_Fmap_agg {S : Set (Esp_har m)} {F : Esp_har m → Esp_har k}
    {F' : Esp_har m →L[ℝ] Esp_har k} {x : Esp_har m} (δ : ℝ)
    (hF' : HasFDerivWithinAt F F' S x) :
    HasFDerivWithinAt (Fmap_agg δ F) (FmapDeriv_agg F' δ) S x := by
  set L : (Esp_har k × Esp_har m) →L[ℝ] Plift_agg k m :=
    (WithLp.linearEquiv 2 ℝ (Esp_har k × Esp_har m)).symm.toContinuousLinearEquiv.toContinuousLinearMap
    with hLdef
  have hgprime : HasFDerivWithinAt (fun y => (F y, δ • y))
      (F'.prod (δ • ContinuousLinearMap.id ℝ (Esp_har m))) S x :=
    hF'.prodMk ((δ • ContinuousLinearMap.id ℝ (Esp_har m)).hasFDerivAt.hasFDerivWithinAt)
  have hHmap : HasFDerivWithinAt (fun y => (WithLp.toLp 2 (F y, δ • y) : Plift_agg k m)) (Hmap_agg F' δ) S x := by
    have := L.hasFDerivAt.comp_hasFDerivWithinAt x hgprime
    convert this using 1
  exact (eLift_agg k m).toContinuousLinearEquiv.hasFDerivAt.comp_hasFDerivWithinAt x hHmap

theorem Hmap_injective_agg (A : Esp_har m →L[ℝ] Esp_har k) {δ : ℝ} (hδ : δ ≠ 0) :
    Function.Injective (Hmap_agg A δ) := by
  intro v w hvw
  rw [Hmap_apply_agg, Hmap_apply_agg] at hvw
  have heq := congrArg WithLp.ofLp hvw
  simp only at heq
  have h2 : δ • v = δ • w := (Prod.ext_iff.mp heq).2
  have h3 := congrArg (fun z => δ⁻¹ • z) h2
  simpa [smul_smul, inv_mul_cancel₀ hδ] using h3

theorem FmapDeriv_injective_agg (A : Esp_har m →L[ℝ] Esp_har k) {δ : ℝ} (hδ : δ ≠ 0) :
    Function.Injective (FmapDeriv_agg A δ) :=
  (eLift_agg k m).injective.comp (Hmap_injective_agg A hδ)

theorem Fmap_injOn_agg (δ : ℝ) (hδ : δ ≠ 0) (F : Esp_har m → Esp_har k) (T : Set (Esp_har m)) :
    InjOn (Fmap_agg δ F) T := by
  intro x _ y _ hxy
  have heq := congrArg (eLift_agg k m).symm hxy
  simp only [Fmap_agg, LinearIsometryEquiv.symm_apply_apply] at heq
  have heq2 := congrArg WithLp.ofLp heq
  simp only at heq2
  have h2 : δ • x = δ • y := (Prod.ext_iff.mp heq2).2
  have h3 := congrArg (fun z => δ⁻¹ • z) h2
  simpa [smul_smul, inv_mul_cancel₀ hδ] using h3

def projLift_agg (k m : ℕ) : Esp_har (k + m) → Esp_har k := fun z => ((eLift_agg k m).symm z).fst

theorem projLift_lipschitz_agg (k m : ℕ) : LipschitzWith 1 (projLift_agg k m) := by
  refine LipschitzWith.of_dist_le_mul fun z z' => ?_
  simp only [NNReal.coe_one, one_mul, projLift_agg, dist_eq_norm]
  rw [← WithLp.sub_fst]
  calc ‖((eLift_agg k m).symm z - (eLift_agg k m).symm z').fst‖
      ≤ ‖(eLift_agg k m).symm z - (eLift_agg k m).symm z'‖ := WithLp.norm_fst_le (Esp_har k) _
    _ = ‖(eLift_agg k m).symm (z - z')‖ := by rw [map_sub]
    _ = ‖z - z'‖ := (eLift_agg k m).symm.norm_map _

theorem projLift_comp_Fmap_agg (δ : ℝ) (F : Esp_har m → Esp_har k) (x : Esp_har m) :
    projLift_agg k m (Fmap_agg δ F x) = F x := by
  simp [projLift_agg, Fmap_agg, WithLp.fst]

theorem gramDet_FmapDeriv_eq_agg (A : Esp_har m →L[ℝ] Esp_har k) (δ : ℝ) :
    gramDet (FmapDeriv_agg A δ) =
      LinearMap.det ((ContinuousLinearMap.adjoint (Hmap_agg A δ)).comp (Hmap_agg A δ) :
        Esp_har m →ₗ[ℝ] Esp_har m) := by
  have hkey : (ContinuousLinearMap.adjoint (FmapDeriv_agg A δ)).comp (FmapDeriv_agg A δ)
      = (ContinuousLinearMap.adjoint (Hmap_agg A δ)).comp (Hmap_agg A δ) := by
    refine ContinuousLinearMap.ext fun w => ?_
    apply ext_inner_left ℝ
    intro v
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
    show (inner ℝ ((eLift_agg k m) (Hmap_agg A δ v)) ((eLift_agg k m) (Hmap_agg A δ w)) : ℝ) = _
    rw [(eLift_agg k m).inner_map_map, ← ContinuousLinearMap.adjoint_inner_right,
      ← ContinuousLinearMap.comp_apply]
  show LinearMap.det (((ContinuousLinearMap.adjoint (FmapDeriv_agg A δ)).comp (FmapDeriv_agg A δ) :
      Esp_har m →L[ℝ] Esp_har m) : Esp_har m →ₗ[ℝ] Esp_har m) = _
  rw [hkey]

theorem Hmap_adjoint_comp_agg (A : Esp_har m →L[ℝ] Esp_har k) (δ : ℝ) :
    (ContinuousLinearMap.adjoint (Hmap_agg A δ)).comp (Hmap_agg A δ)
      = (ContinuousLinearMap.adjoint A).comp A + δ^2 • ContinuousLinearMap.id ℝ (Esp_har m) := by
  refine ContinuousLinearMap.ext fun w => ?_
  apply ext_inner_left ℝ
  intro v
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  show (inner ℝ (Hmap_agg A δ v) (Hmap_agg A δ w) : ℝ) = _
  have hinner : (inner ℝ (Hmap_agg A δ v) (Hmap_agg A δ w) : ℝ) = inner ℝ (A v) (A w) + δ^2 * inner ℝ v w := by
    rw [Hmap_apply_agg, Hmap_apply_agg, WithLp.prod_inner_apply]
    show (inner ℝ (A v) (A w) : ℝ) + inner ℝ (δ • v) (δ • w) = _
    rw [inner_smul_left, inner_smul_right]
    simp [sq]; ring
  rw [hinner, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    inner_add_right, ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_id', id_eq, inner_smul_right]

theorem detOfDiag_agg {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ (Esp_har n))
    (T : Esp_har n →ₗ[ℝ] Esp_har n) (μ : Fin n → ℝ) (hb : ∀ i, T (b i) = μ i • b i) :
    LinearMap.det T = ∏ i, μ i := by
  rw [← LinearMap.det_toMatrix b.toBasis]
  have hmat : LinearMap.toMatrix b.toBasis b.toBasis T = Matrix.diagonal μ := by
    ext i j
    rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis, hb j, map_smul,
      ← OrthonormalBasis.coe_toBasis, Basis.repr_self]
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_apply,
      Matrix.diagonal_apply]
    by_cases hij : j = i
    · simp [hij]
    · simp [hij, Ne.symm hij]
  rw [hmat, Matrix.det_diagonal]

theorem gramDet_nonneg_agg (A : Esp_har m →L[ℝ] Esp_har k) : 0 ≤ gramDet A := by
  have hpos : ((ContinuousLinearMap.adjoint A).comp A).IsPositive :=
    ContinuousLinearMap.isPositive_adjoint_comp_self A
  have hsymm : (((ContinuousLinearMap.adjoint A).comp A : Esp_har m →L[ℝ] Esp_har m) :
      Esp_har m →ₗ[ℝ] Esp_har m).IsSymmetric := hpos.toLinearMap.isSymmetric
  have hn : Module.finrank ℝ (Esp_har m) = m := finrank_euclideanSpace_fin
  set b := hsymm.eigenvectorBasis hn
  set μ := hsymm.eigenvalues hn
  have hnonneg : ∀ i, 0 ≤ μ i := by
    intro i
    have h1 : (((ContinuousLinearMap.adjoint A).comp A : Esp_har m →L[ℝ] Esp_har m) :
        Esp_har m →ₗ[ℝ] Esp_har m) (b i) = μ i • b i := hsymm.apply_eigenvectorBasis hn i
    have h2 : (0:ℝ) ≤ inner ℝ (((ContinuousLinearMap.adjoint A).comp A :
        Esp_har m →L[ℝ] Esp_har m) (b i)) (b i) := hpos.inner_nonneg_left (b i)
    rw [show (((ContinuousLinearMap.adjoint A).comp A : Esp_har m →L[ℝ] Esp_har m) (b i))
      = μ i • b i from h1] at h2
    rw [inner_smul_left] at h2
    simp only [RCLike.conj_to_real] at h2
    have hbi : (inner ℝ (b i) (b i) : ℝ) = 1 := by
      rw [real_inner_self_eq_norm_sq]
      have := b.orthonormal.1 i
      rw [this]; norm_num
    rwa [hbi, mul_one] at h2
  have hdet : gramDet A = ∏ i, μ i :=
    detOfDiag_agg b (((ContinuousLinearMap.adjoint A).comp A : Esp_har m →L[ℝ] Esp_har m) :
        Esp_har m →ₗ[ℝ] Esp_har m) μ (fun i => hsymm.apply_eigenvectorBasis hn i)
  rw [hdet]
  exact Finset.prod_nonneg fun i _ => hnonneg i

/-- Injectivity of `A` is equivalent to positivity of `gramDet A`. -/
theorem gramDet_pos_iff_injective_agg (A : Esp_har m →L[ℝ] Esp_har k) :
    0 < gramDet A ↔ Function.Injective A := by
  set T : Esp_har m →L[ℝ] Esp_har m := (ContinuousLinearMap.adjoint A).comp A with hTdef
  have hTA : ∀ x, T x = 0 ↔ A x = 0 := by
    intro x
    constructor
    · intro hTx
      have h1 : (inner ℝ (T x) x : ℝ) = 0 := by rw [hTx]; simp
      have h2 : ‖A x‖ ^ 2 = inner ℝ (T x) x := by
        have := ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left A x
        simpa [hTdef, RCLike.re_to_real] using this
      have h3 : ‖A x‖ = 0 := by
        have : ‖A x‖ ^ 2 = 0 := by rw [h2, h1]
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      exact norm_eq_zero.mp h3
    · intro hAx
      show (ContinuousLinearMap.adjoint A) (A x) = 0
      rw [hAx, map_zero]
  have hTinj_iff : Function.Injective T ↔ Function.Injective A := by
    constructor
    · intro hTinj x y hxy
      apply hTinj
      have hA0 : A (x - y) = 0 := by rw [map_sub, hxy]; abel
      have hT0 : T (x - y) = 0 := (hTA (x - y)).mpr hA0
      rw [map_sub] at hT0
      exact sub_eq_zero.mp hT0
    · intro hAinj x y hxy
      apply hAinj
      have hT0 : T (x - y) = 0 := by rw [map_sub, hxy]; abel
      have hA0 : A (x - y) = 0 := (hTA (x - y)).mp hT0
      rw [map_sub] at hA0
      exact sub_eq_zero.mp hA0
  have hgd0 : gramDet A = 0 ↔ ¬ Function.Injective A := by
    rw [← hTinj_iff]
    show LinearMap.det (T : Esp_har m →ₗ[ℝ] Esp_har m) = 0 ↔ _
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot]
    exact not_congr LinearMap.ker_eq_bot
  constructor
  · intro hpos
    by_contra hninj
    rw [hgd0.mpr hninj] at hpos
    exact lt_irrefl 0 hpos
  · intro hinj
    rcases (gramDet_nonneg_agg A).lt_or_eq with h | h
    · exact h
    · exact absurd hinj (hgd0.mp h.symm)

theorem gramDetShift_bound_agg (A : Esp_har m →L[ℝ] Esp_har k) (hA0 : gramDet A = 0) {δ : ℝ}
    (hδ : 0 < δ) :
    LinearMap.det ((((ContinuousLinearMap.adjoint A).comp A : Esp_har m →L[ℝ] Esp_har m) :
        Esp_har m →ₗ[ℝ] Esp_har m) + δ ^ 2 • LinearMap.id)
      ≤ δ ^ 2 * (‖A‖ ^ 2 + δ ^ 2) ^ (m - 1) := by
  have hpos : ((ContinuousLinearMap.adjoint A).comp A).IsPositive :=
    ContinuousLinearMap.isPositive_adjoint_comp_self A
  have hsymm : (((ContinuousLinearMap.adjoint A).comp A : Esp_har m →L[ℝ] Esp_har m) :
      Esp_har m →ₗ[ℝ] Esp_har m).IsSymmetric := hpos.toLinearMap.isSymmetric
  have hn : Module.finrank ℝ (Esp_har m) = m := finrank_euclideanSpace_fin
  set b := hsymm.eigenvectorBasis hn
  set μ := hsymm.eigenvalues hn
  set T' : Esp_har m →ₗ[ℝ] Esp_har m :=
    (((ContinuousLinearMap.adjoint A).comp A : Esp_har m →L[ℝ] Esp_har m) :
        Esp_har m →ₗ[ℝ] Esp_har m) + δ ^ 2 • LinearMap.id with hT'def
  have hTbi : ∀ i, (((ContinuousLinearMap.adjoint A).comp A : Esp_har m →L[ℝ] Esp_har m) :
      Esp_har m →ₗ[ℝ] Esp_har m) (b i) = μ i • b i := fun i => hsymm.apply_eigenvectorBasis hn i
  have hnonneg : ∀ i, 0 ≤ μ i := by
    intro i
    have h2 : (0:ℝ) ≤ inner ℝ (((ContinuousLinearMap.adjoint A).comp A :
        Esp_har m →L[ℝ] Esp_har m) (b i)) (b i) := hpos.inner_nonneg_left (b i)
    rw [show (((ContinuousLinearMap.adjoint A).comp A : Esp_har m →L[ℝ] Esp_har m) (b i))
      = μ i • b i from hTbi i, inner_smul_left] at h2
    simp only [RCLike.conj_to_real] at h2
    have hbi : (inner ℝ (b i) (b i) : ℝ) = 1 := by
      rw [real_inner_self_eq_norm_sq]
      have := b.orthonormal.1 i
      rw [this]; norm_num
    rwa [hbi, mul_one] at h2
  have hnormbound : ∀ i, μ i ≤ ‖A‖ ^ 2 := by
    intro i
    have hTnorm : ‖((ContinuousLinearMap.adjoint A).comp A : Esp_har m →L[ℝ] Esp_har m)‖
        = ‖A‖ * ‖A‖ := ContinuousLinearMap.norm_adjoint_comp_self A
    have h1 : (((ContinuousLinearMap.adjoint A).comp A : Esp_har m →L[ℝ] Esp_har m) : Esp_har m →L[ℝ] Esp_har m) (b i)
        = μ i • b i := hTbi i
    have hnorm1 : ‖(((ContinuousLinearMap.adjoint A).comp A : Esp_har m →L[ℝ] Esp_har m) : Esp_har m →L[ℝ] Esp_har m) (b i)‖
        = |μ i| * ‖b i‖ := by rw [h1, norm_smul]; simp [Real.norm_eq_abs]
    have hnormbi : ‖b i‖ = 1 := b.orthonormal.1 i
    rw [hnormbi, mul_one] at hnorm1
    have hle : ‖(((ContinuousLinearMap.adjoint A).comp A : Esp_har m →L[ℝ] Esp_har m) : Esp_har m →L[ℝ] Esp_har m) (b i)‖
        ≤ ‖((ContinuousLinearMap.adjoint A).comp A : Esp_har m →L[ℝ] Esp_har m)‖ * ‖b i‖ :=
      ContinuousLinearMap.le_opNorm _ (b i)
    rw [hnormbi, mul_one, hnorm1, hTnorm, ← sq] at hle
    calc μ i ≤ |μ i| := le_abs_self _
      _ ≤ ‖A‖ ^ 2 := hle
  have hdet0 : ∏ i, μ i = 0 := by
    rw [← detOfDiag_agg b _ μ hTbi]; exact hA0
  obtain ⟨i0, -, hi0⟩ := Finset.prod_eq_zero_iff.mp hdet0
  have hshift : ∀ i, T' (b i) = (μ i + δ ^ 2) • b i := by
    intro i
    rw [hT'def]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, hTbi i]
    rw [add_smul]
  show LinearMap.det T' ≤ _
  rw [detOfDiag_agg b T' (fun i => μ i + δ ^ 2) hshift]
  have hsplit : ∏ i, (μ i + δ ^ 2) = (μ i0 + δ ^ 2) * ∏ i ∈ Finset.univ.erase i0, (μ i + δ ^ 2) :=
    (Finset.mul_prod_erase Finset.univ (fun i => μ i + δ ^ 2) (Finset.mem_univ i0)).symm
  rw [hsplit, hi0, zero_add]
  have hcard : (Finset.univ.erase i0).card = m - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i0), Finset.card_univ, Fintype.card_fin]
  have hbound : ∏ i ∈ Finset.univ.erase i0, (μ i + δ ^ 2) ≤ ∏ _i ∈ Finset.univ.erase i0, (‖A‖ ^ 2 + δ ^ 2) := by
    apply Finset.prod_le_prod
    · intro i _; have := hnonneg i; positivity
    · intro i _; have := hnormbound i; linarith
  rw [Finset.prod_const, hcard] at hbound
  have hδ2 : (0:ℝ) ≤ δ ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_left hbound hδ2

/-- Differentiable images of `μH[m]`-null measurable sets are `μH[m]`-null. -/
theorem nullSetImage_agg {T : Set (Esp_har m)} {F : Esp_har m → Esp_har k}
    {F' : Esp_har m → Esp_har m →L[ℝ] Esp_har k}
    (hTmeas : MeasurableSet T) (hF' : ∀ x ∈ T, HasFDerivWithinAt F (F' x) T x)
    (hT0 : (μH[(m:ℝ)] : Measure (Esp_har m)) T = 0) :
    (μH[(m:ℝ)] : Measure (Esp_har k)) (F '' T) = 0 := by
  have hFδderiv : ∀ x ∈ T, HasFDerivWithinAt (Fmap_agg 1 F) (FmapDeriv_agg (F' x) 1) T x :=
    fun x hx => hasFDerivWithinAt_Fmap_agg 1 (hF' x hx)
  have hFδ'inj : ∀ x ∈ T, Function.Injective (FmapDeriv_agg (F' x) 1) :=
    fun x _ => FmapDeriv_injective_agg (F' x) one_ne_zero
  have hFδinjOn : InjOn (Fmap_agg 1 F) T := Fmap_injOn_agg 1 one_ne_zero F T
  have harea := areaFormulaInj_agi m (k + m) T (Fmap_agg 1 F) (fun x => FmapDeriv_agg (F' x) 1)
    hTmeas hFδderiv hFδinjOn hFδ'inj
  have hint0 : (∫⁻ x in T, ENNReal.ofReal (Real.sqrt (gramDet (FmapDeriv_agg (F' x) 1)))
      ∂(μH[(m:ℝ)] : Measure (Esp_har m))) = 0 := setLIntegral_measure_zero T _ hT0
  rw [hint0] at harea
  have hproj : F '' T = projLift_agg k m '' (Fmap_agg 1 F '' T) := by
    rw [show projLift_agg k m '' (Fmap_agg 1 F '' T) = (projLift_agg k m ∘ Fmap_agg 1 F) '' T from
      (Set.image_comp (projLift_agg k m) (Fmap_agg 1 F) T).symm]
    apply Set.image_congr
    intro x _
    exact (projLift_comp_Fmap_agg 1 F x).symm
  rw [hproj]
  refine le_antisymm ?_ (zero_le _)
  calc (μH[(m:ℝ)] : Measure (Esp_har k)) (projLift_agg k m '' (Fmap_agg 1 F '' T))
      ≤ (1 : ℝ≥0∞) ^ (m:ℝ) * (μH[(m:ℝ)] : Measure (Esp_har (k + m))) (Fmap_agg 1 F '' T) :=
        (projLift_lipschitz_agg k m).hausdorffMeasure_image_le (Nat.cast_nonneg m) _
    _ = 0 := by rw [harea]; simp

/-- The image of the "bounded critical set" `N` (a measurable subset of `S`, of bounded radius `M`,
on which `gramDet ∘ F'` vanishes and `‖F' ·‖` is bounded by `M`) has `μH[m]`-null image. -/
theorem criticalSetPiece_image_zero_agg {S : Set (Esp_har m)} {F : Esp_har m → Esp_har k}
    {F' : Esp_har m → Esp_har m →L[ℝ] Esp_har k} (hF' : ∀ x ∈ S, HasFDerivWithinAt F (F' x) S x)
    {N : Set (Esp_har m)} (hNmeas : MeasurableSet N) (hNS : N ⊆ S) {M : ℝ} (_hM : 0 ≤ M)
    (hNball : N ⊆ closedBall 0 M)
    (hNprop : ∀ x ∈ N, gramDet (F' x) = 0 ∧ ‖F' x‖ ≤ M) :
    (μH[(m:ℝ)] : Measure (Esp_har k)) (F '' N) = 0 := by
  have hNfin : (μH[(m:ℝ)] : Measure (Esp_har m)) N ≠ ∞ := by
    have hV := hausdorffVolume_hlin m
    have hballfin : (μH[(m:ℝ)] : Measure (Esp_har m)) (closedBall (0 : Esp_har m) M) < ∞ := by
      rw [hV.1, Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top hV.2.2 measure_closedBall_lt_top
    exact ((measure_mono hNball).trans_lt hballfin).ne
  -- the bound, for a fixed δ > 0
  have hbound : ∀ δ : ℝ, 0 < δ →
      (μH[(m:ℝ)] : Measure (Esp_har k)) (F '' N)
        ≤ ENNReal.ofReal (Real.sqrt (δ ^ 2 * (M ^ 2 + δ ^ 2) ^ (m - 1)))
          * (μH[(m:ℝ)] : Measure (Esp_har m)) N := by
    intro δ hδ
    have hFδderiv : ∀ x ∈ N, HasFDerivWithinAt (Fmap_agg δ F) (FmapDeriv_agg (F' x) δ) N x :=
      fun x hx => (hasFDerivWithinAt_Fmap_agg δ (hF' x (hNS hx))).mono hNS
    have hFδ'inj : ∀ x ∈ N, Function.Injective (FmapDeriv_agg (F' x) δ) :=
      fun x _ => FmapDeriv_injective_agg (F' x) hδ.ne'
    have hFδinjOn : InjOn (Fmap_agg δ F) N := Fmap_injOn_agg δ hδ.ne' F N
    have harea := areaFormulaInj_agi m (k + m) N (Fmap_agg δ F) (fun x => FmapDeriv_agg (F' x) δ)
      hNmeas hFδderiv hFδinjOn hFδ'inj
    have hptbound : ∀ x ∈ N, ENNReal.ofReal (Real.sqrt (gramDet (FmapDeriv_agg (F' x) δ)))
        ≤ ENNReal.ofReal (Real.sqrt (δ ^ 2 * (M ^ 2 + δ ^ 2) ^ (m - 1))) := by
      intro x hx
      apply ENNReal.ofReal_le_ofReal
      apply Real.sqrt_le_sqrt
      rw [gramDet_FmapDeriv_eq_agg, Hmap_adjoint_comp_agg]
      have hgd0 : gramDet (F' x) = 0 := (hNprop x hx).1
      have hFx : ‖F' x‖ ≤ M := (hNprop x hx).2
      calc LinearMap.det ((((ContinuousLinearMap.adjoint (F' x)).comp (F' x) :
              Esp_har m →L[ℝ] Esp_har m) : Esp_har m →ₗ[ℝ] Esp_har m) + δ ^ 2 • LinearMap.id)
          ≤ δ ^ 2 * (‖F' x‖ ^ 2 + δ ^ 2) ^ (m - 1) := gramDetShift_bound_agg (F' x) hgd0 hδ
        _ ≤ δ ^ 2 * (M ^ 2 + δ ^ 2) ^ (m - 1) := by
            gcongr
    have hintbound : (∫⁻ x in N, ENNReal.ofReal (Real.sqrt (gramDet (FmapDeriv_agg (F' x) δ)))
        ∂(μH[(m:ℝ)] : Measure (Esp_har m)))
        ≤ ENNReal.ofReal (Real.sqrt (δ ^ 2 * (M ^ 2 + δ ^ 2) ^ (m - 1)))
          * (μH[(m:ℝ)] : Measure (Esp_har m)) N := by
      calc (∫⁻ x in N, ENNReal.ofReal (Real.sqrt (gramDet (FmapDeriv_agg (F' x) δ)))
            ∂(μH[(m:ℝ)] : Measure (Esp_har m)))
          ≤ ∫⁻ _x in N, ENNReal.ofReal (Real.sqrt (δ ^ 2 * (M ^ 2 + δ ^ 2) ^ (m - 1)))
            ∂(μH[(m:ℝ)] : Measure (Esp_har m)) := by
            apply lintegral_mono_ae
            filter_upwards [ae_restrict_mem hNmeas] with x hx using hptbound x hx
        _ = ENNReal.ofReal (Real.sqrt (δ ^ 2 * (M ^ 2 + δ ^ 2) ^ (m - 1)))
            * (μH[(m:ℝ)] : Measure (Esp_har m)) N := setLIntegral_const _ _
    have hFδNmeas : (μH[(m:ℝ)] : Measure (Esp_har (k + m))) (Fmap_agg δ F '' N)
        ≤ ENNReal.ofReal (Real.sqrt (δ ^ 2 * (M ^ 2 + δ ^ 2) ^ (m - 1)))
          * (μH[(m:ℝ)] : Measure (Esp_har m)) N := harea ▸ hintbound
    have hproj : F '' N = projLift_agg k m '' (Fmap_agg δ F '' N) := by
      rw [show projLift_agg k m '' (Fmap_agg δ F '' N) = (projLift_agg k m ∘ Fmap_agg δ F) '' N from
        (Set.image_comp (projLift_agg k m) (Fmap_agg δ F) N).symm]
      apply Set.image_congr
      intro x _
      exact (projLift_comp_Fmap_agg δ F x).symm
    rw [hproj]
    calc (μH[(m:ℝ)] : Measure (Esp_har k)) (projLift_agg k m '' (Fmap_agg δ F '' N))
        ≤ (1 : ℝ≥0∞) ^ (m:ℝ) * (μH[(m:ℝ)] : Measure (Esp_har (k + m))) (Fmap_agg δ F '' N) :=
          (projLift_lipschitz_agg k m).hausdorffMeasure_image_le (Nat.cast_nonneg m) _
      _ ≤ ENNReal.ofReal (Real.sqrt (δ ^ 2 * (M ^ 2 + δ ^ 2) ^ (m - 1)))
            * (μH[(m:ℝ)] : Measure (Esp_har m)) N := by
          rw [ENNReal.one_rpow, one_mul]; exact hFδNmeas
  -- take δ → 0
  have hc : Continuous (fun δ : ℝ => δ ^ 2 * (M ^ 2 + δ ^ 2) ^ (m - 1)) := by fun_prop
  have hpoly0 : Tendsto (fun δ : ℝ => δ ^ 2 * (M ^ 2 + δ ^ 2) ^ (m - 1)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h0 : Tendsto (fun δ : ℝ => δ ^ 2 * (M ^ 2 + δ ^ 2) ^ (m - 1)) (𝓝 (0:ℝ))
        (𝓝 (0 ^ 2 * (M ^ 2 + 0 ^ 2) ^ (m - 1))) := hc.tendsto 0
    have h0' : Tendsto (fun δ : ℝ => δ ^ 2 * (M ^ 2 + δ ^ 2) ^ (m - 1)) (𝓝 (0:ℝ)) (𝓝 0) := by
      simpa using h0
    exact h0'.mono_left nhdsWithin_le_nhds
  have hcont : Tendsto (fun δ : ℝ => Real.sqrt (δ ^ 2 * (M ^ 2 + δ ^ 2) ^ (m - 1)))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hpoly0
    simpa using this
  have h1 : Tendsto (fun δ : ℝ => ENNReal.ofReal (Real.sqrt (δ ^ 2 * (M ^ 2 + δ ^ 2) ^ (m - 1))))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have := (ENNReal.continuous_ofReal.tendsto 0).comp hcont
    simpa using this
  have htendsto : Tendsto (fun δ : ℝ =>
      ENNReal.ofReal (Real.sqrt (δ ^ 2 * (M ^ 2 + δ ^ 2) ^ (m - 1)))
        * (μH[(m:ℝ)] : Measure (Esp_har m)) N) (𝓝[>] 0) (𝓝 0) := by
    have := ENNReal.Tendsto.mul_const h1 (Or.inr hNfin)
    simpa using this
  refine le_antisymm (ge_of_tendsto htendsto ?_) (zero_le _)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [mem_Ioi] at hδ
  exact hbound δ hδ

theorem aemeasurableFderivWithin_agg {S : Set (Esp_har m)} {F : Esp_har m → Esp_har k}
    {F' : Esp_har m → Esp_har m →L[ℝ] Esp_har k} (hs : MeasurableSet S)
    (hf' : ∀ x ∈ S, HasFDerivWithinAt F (F' x) S x) :
    AEMeasurable F' (μH[(m:ℝ)].restrict S) := by
  refine aemeasurable_of_unif_approx fun ε εpos => ?_
  let δ : ℝ≥0 := ⟨ε, le_of_lt εpos⟩
  have δpos : 0 < δ := εpos
  obtain ⟨t, A, t_disj, t_meas, t_cover, ht, -⟩ :
    ∃ (t : ℕ → Set (Esp_har m)) (A : ℕ → Esp_har m →L[ℝ] Esp_har k),
      Pairwise (Disjoint on t) ∧
        (∀ n : ℕ, MeasurableSet (t n)) ∧
          (S ⊆ ⋃ n : ℕ, t n) ∧
            (∀ n : ℕ, ApproximatesLinearOn F (A n) (S ∩ t n) δ) ∧
              (S.Nonempty → ∀ n, ∃ y ∈ S, A n = F' y) :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt F S F' hf' (fun _ => δ) fun _ =>
      δpos.ne'
  obtain ⟨g, g_meas, hg⟩ :
      ∃ g : Esp_har m → (Esp_har m →L[ℝ] Esp_har k), Measurable g ∧
        ∀ (n : ℕ) (x : Esp_har m), x ∈ t n → g x = A n :=
    exists_measurable_piecewise t t_meas (fun n _ => A n) (fun n => measurable_const) <|
      t_disj.mono fun i j h => by simp only [h.inter_eq, eqOn_empty]
  refine ⟨g, g_meas.aemeasurable, ?_⟩
  suffices H : ∀ᵐ x : Esp_har m ∂sum fun n ↦ (μH[(m:ℝ)] : Measure (Esp_har m)).restrict (S ∩ t n),
      dist (g x) (F' x) ≤ ε by
    have hle : (μH[(m:ℝ)] : Measure (Esp_har m)).restrict S ≤
        sum fun n => (μH[(m:ℝ)] : Measure (Esp_har m)).restrict (S ∩ t n) := by
      have hScov : S = ⋃ n, S ∩ t n := by
        rw [← inter_iUnion]
        exact Subset.antisymm (subset_inter Subset.rfl t_cover) inter_subset_left
      conv_lhs => rw [hScov]
      exact restrict_iUnion_le
    exact ae_mono hle H
  refine ae_sum_iff.2 fun n => ?_
  have E₁ : ∀ᵐ x : Esp_har m ∂(μH[(m:ℝ)] : Measure (Esp_har m)).restrict (S ∩ t n),
      ‖F' x - A n‖₊ ≤ δ :=
    approxLinearOnNormFderivWithinSubLe_agi (ht n) (hs.inter (t_meas n)) F'
      fun x hx => (hf' x hx.1).mono inter_subset_left
  have E₂ : ∀ᵐ x : Esp_har m ∂(μH[(m:ℝ)] : Measure (Esp_har m)).restrict (S ∩ t n), g x = A n := by
    suffices H : ∀ᵐ x : Esp_har m ∂(μH[(m:ℝ)] : Measure (Esp_har m)).restrict (t n), g x = A n from
      ae_mono (restrict_mono inter_subset_right le_rfl) H
    filter_upwards [ae_restrict_mem (t_meas n)]
    exact hg n
  filter_upwards [E₁, E₂] with x hx1 hx2
  rw [← nndist_eq_nnnorm] at hx1
  rw [hx2, dist_comm]
  exact hx1

/-- **The critical/degenerate set has null image.** For measurable `S`, `F'` defined within `S`
(`HasFDerivWithinAt`, no continuity), there is a measurable `μH[m]`-null set `Bad` such that the
image, under `F`, of the "genuinely degenerate part of `S` away from `Bad`"
(`(S \ Bad) ∩ {x | gramDet (F' x) = 0}`) is `μH[m]`-null. -/
theorem criticalSetFull_agg {S : Set (Esp_har m)} {F : Esp_har m → Esp_har k}
    {F' : Esp_har m → Esp_har m →L[ℝ] Esp_har k} (hSmeas : MeasurableSet S)
    (hF' : ∀ x ∈ S, HasFDerivWithinAt F (F' x) S x) :
    ∃ Bad : Set (Esp_har m), MeasurableSet Bad ∧ (μH[(m:ℝ)] : Measure (Esp_har m)) Bad = 0 ∧
      MeasurableSet ((S \ Bad) ∩ {x | gramDet (F' x) = 0}) ∧
      (μH[(m:ℝ)] : Measure (Esp_har k))
        (F '' ((S \ Bad) ∩ {x | gramDet (F' x) = 0})) = 0 := by
  have hAE : AEMeasurable F' (μH[(m:ℝ)].restrict S) := aemeasurableFderivWithin_agg hSmeas hF'
  set G := hAE.mk F' with hGdef
  have hGmeas : Measurable G := hAE.measurable_mk
  have hae : F' =ᵐ[(μH[(m:ℝ)] : Measure (Esp_har m)).restrict S] G := hAE.ae_eq_mk
  have hmis : (μH[(m:ℝ)] : Measure (Esp_har m)).restrict S {x | F' x ≠ G x} = 0 := hae
  have hmis' : (μH[(m:ℝ)] : Measure (Esp_har m)) ({x | F' x ≠ G x} ∩ S) = 0 := by
    rwa [Measure.restrict_apply' hSmeas] at hmis
  obtain ⟨Bad, hBadsup, hBadmeas, hBad0⟩ := exists_measurable_superset_of_null hmis'
  have hcov : ∀ x ∈ S, x ∉ Bad → F' x = G x := by
    intro x hxS hxBad
    by_contra hne
    exact hxBad (hBadsup ⟨hne, hxS⟩)
  set Z0 := (S \ Bad) ∩ {x | gramDet (G x) = 0} with hZ0def
  have hZ0eq : (S \ Bad) ∩ {x | gramDet (F' x) = 0} = Z0 := by
    ext x
    simp only [hZ0def, mem_inter_iff, mem_diff, mem_setOf_eq]
    constructor
    · rintro ⟨⟨hxS, hxBad⟩, hgd⟩
      exact ⟨⟨hxS, hxBad⟩, by rw [← hcov x hxS hxBad]; exact hgd⟩
    · rintro ⟨⟨hxS, hxBad⟩, hgd⟩
      exact ⟨⟨hxS, hxBad⟩, by rw [hcov x hxS hxBad]; exact hgd⟩
  have hZ0meas : MeasurableSet Z0 := by
    refine (hSmeas.diff hBadmeas).inter ?_
    exact (gramDet_continuous_har.measurable.comp hGmeas) measurableSet_eq
  refine ⟨Bad, hBadmeas, hBad0, hZ0eq ▸ hZ0meas, ?_⟩
  rw [hZ0eq]
  have hZ0S : Z0 ⊆ S := fun x hx => hx.1.1
  set N : ℕ → Set (Esp_har m) := fun M =>
      Z0 ∩ {x | ‖G x‖ ≤ (M : ℝ)} ∩ closedBall (0 : Esp_har m) (M : ℝ) with hNdef
  have hNmeas : ∀ M, MeasurableSet (N M) := by
    intro M
    exact (hZ0meas.inter ((continuous_norm.measurable.comp hGmeas) measurableSet_Iic)).inter
      measurableSet_closedBall
  have hNS : ∀ M, N M ⊆ S := fun M => (inter_subset_left.trans inter_subset_left).trans hZ0S
  have hNball : ∀ M : ℕ, N M ⊆ closedBall (0 : Esp_har m) (M : ℝ) := fun M => inter_subset_right
  have hNprop : ∀ M : ℕ, ∀ x ∈ N M, gramDet (F' x) = 0 ∧ ‖F' x‖ ≤ (M : ℝ) := by
    intro M x hx
    obtain ⟨⟨⟨⟨hxS, hxBad⟩, hgd⟩, hxnorm⟩, -⟩ := hx
    have hFG : F' x = G x := hcov x hxS hxBad
    exact ⟨by rw [hFG]; exact hgd, by rw [hFG]; exact hxnorm⟩
  have hstep : ∀ M : ℕ, (μH[(m:ℝ)] : Measure (Esp_har k)) (F '' N M) = 0 := fun M =>
    criticalSetPiece_image_zero_agg hF' (hNmeas M) (hNS M)
      (Nat.cast_nonneg M) (hNball M) (hNprop M)
  have hZ0cov : Z0 = ⋃ M : ℕ, N M := by
    refine Subset.antisymm ?_ ?_
    · intro x hx
      set M : ℕ := ⌈max ‖G x‖ ‖x‖⌉₊ with hMdef
      refine mem_iUnion.mpr ⟨M, ⟨hx, ?_⟩, ?_⟩
      · exact le_trans (le_max_left ‖G x‖ ‖x‖) (Nat.le_ceil (max ‖G x‖ ‖x‖))
      · rw [mem_closedBall, dist_zero_right]
        exact le_trans (le_max_right ‖G x‖ ‖x‖) (Nat.le_ceil (max ‖G x‖ ‖x‖))
    · intro x hx
      obtain ⟨M, hM⟩ := mem_iUnion.mp hx
      exact hM.1.1
  rw [hZ0cov, Set.image_iUnion]
  refine le_antisymm ?_ (zero_le _)
  calc (μH[(m:ℝ)] : Measure (Esp_har k)) (⋃ M, F '' N M)
      ≤ ∑' M, (μH[(m:ℝ)] : Measure (Esp_har k)) (F '' N M) := measure_iUnion_le _
    _ = 0 := by simp [hstep]

/-- **The general area formula.** -/
theorem areaFormulaGen_agg (m k : ℕ) : AreaFormulaGenProp m k := by
  intro S F F' hSmeas hF' hInj
  obtain ⟨Bad, hBadmeas, hBad0, hZmeas, hZ0img0⟩ := criticalSetFull_agg hSmeas hF'
  set Zdeg := (S \ Bad) ∩ {x | gramDet (F' x) = 0} with hZdegdef
  set SBad := S ∩ Bad with hSBaddef
  set SPlus := (S \ Bad) ∩ {x | gramDet (F' x) ≠ 0} with hSPdef
  set W := SBad ∪ Zdeg with hWdef
  have hSBadmeas : MeasurableSet SBad := hSmeas.inter hBadmeas
  have hWmeas : MeasurableSet W := hSBadmeas.union hZmeas
  have hSPmeas : MeasurableSet SPlus := by
    have heqdiff : SPlus = (S \ Bad) \ Zdeg := by
      ext x
      simp only [hSPdef, hZdegdef, mem_inter_iff, mem_diff, mem_setOf_eq]
      tauto
    rw [heqdiff]
    exact (hSmeas.diff hBadmeas).diff hZmeas
  have hpart : S = SPlus ∪ W := by
    ext x
    simp only [hSPdef, hSBaddef, hZdegdef, hWdef, mem_union, mem_inter_iff, mem_diff, mem_setOf_eq]
    by_cases hxS : x ∈ S <;> by_cases hxBad : x ∈ Bad <;> tauto
  have hDisjointSW : Disjoint SPlus W := by
    rw [Set.disjoint_left]
    intro x hxSP hxW
    simp only [hSPdef, mem_inter_iff, mem_diff, mem_setOf_eq] at hxSP
    simp only [hWdef, hSBaddef, hZdegdef, mem_union, mem_inter_iff, mem_diff, mem_setOf_eq] at hxW
    tauto
  have hDisjointBZ : Disjoint SBad Zdeg := by
    rw [Set.disjoint_left]
    intro x hxB hxZ
    simp only [hSBaddef, mem_inter_iff] at hxB
    simp only [hZdegdef, mem_inter_iff, mem_diff] at hxZ
    tauto
  have hSPS : SPlus ⊆ S := fun x hx => hx.1.1
  have hSPinjD : ∀ x ∈ SPlus, Function.Injective (F' x) := by
    intro x hx
    rw [← gramDet_pos_iff_injective_agg]
    rcases (gramDet_nonneg_agg (F' x)).lt_or_eq with h | h
    · exact h
    · exact absurd h.symm hx.2
  have hmain := areaFormulaInj_agi m k SPlus F F' hSPmeas
    (fun x hx => (hF' x (hSPS hx)).mono hSPS) (hInj.mono hSPS) hSPinjD
  have hSBad0 : (μH[(m:ℝ)] : Measure (Esp_har m)) SBad = 0 :=
    le_antisymm ((measure_mono inter_subset_right).trans_eq hBad0) (zero_le _)
  have hSBadimg0 : (μH[(m:ℝ)] : Measure (Esp_har k)) (F '' SBad) = 0 :=
    nullSetImage_agg hSBadmeas (fun x hx => (hF' x hx.1).mono (inter_subset_left)) hSBad0
  have hWimg0 : (μH[(m:ℝ)] : Measure (Esp_har k)) (F '' W) = 0 := by
    refine le_antisymm ?_ (zero_le _)
    calc (μH[(m:ℝ)] : Measure (Esp_har k)) (F '' W)
        = (μH[(m:ℝ)] : Measure (Esp_har k)) (F '' SBad ∪ F '' Zdeg) := by
          rw [hWdef, Set.image_union]
      _ ≤ (μH[(m:ℝ)] : Measure (Esp_har k)) (F '' SBad)
          + (μH[(m:ℝ)] : Measure (Esp_har k)) (F '' Zdeg) := measure_union_le _ _
      _ = 0 := by rw [hSBadimg0, hZ0img0]; simp
  have hmeasEq : (μH[(m:ℝ)] : Measure (Esp_har k)) (F '' S)
      = (μH[(m:ℝ)] : Measure (Esp_har k)) (F '' SPlus) := by
    refine le_antisymm ?_ (measure_mono (Set.image_mono hSPS))
    calc (μH[(m:ℝ)] : Measure (Esp_har k)) (F '' S)
        = (μH[(m:ℝ)] : Measure (Esp_har k)) (F '' SPlus ∪ F '' W) := by rw [hpart, Set.image_union]
      _ ≤ (μH[(m:ℝ)] : Measure (Esp_har k)) (F '' SPlus)
          + (μH[(m:ℝ)] : Measure (Esp_har k)) (F '' W) := measure_union_le _ _
      _ = (μH[(m:ℝ)] : Measure (Esp_har k)) (F '' SPlus) := by rw [hWimg0]; simp
  have hZdeg0 : (∫⁻ x in Zdeg, ENNReal.ofReal (Real.sqrt (gramDet (F' x)))
      ∂(μH[(m:ℝ)] : Measure (Esp_har m))) = 0 := by
    have hzero : ∀ x ∈ Zdeg, ENNReal.ofReal (Real.sqrt (gramDet (F' x))) = 0 := by
      intro x hx
      have hgd : gramDet (F' x) = 0 := hx.2
      rw [hgd]; simp
    calc (∫⁻ x in Zdeg, ENNReal.ofReal (Real.sqrt (gramDet (F' x)))
          ∂(μH[(m:ℝ)] : Measure (Esp_har m)))
        = ∫⁻ _x in Zdeg, (0 : ℝ≥0∞) ∂(μH[(m:ℝ)] : Measure (Esp_har m)) := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem hZmeas] with x hx using hzero x hx
      _ = 0 := by simp
  have hSBadint0 : (∫⁻ x in SBad, ENNReal.ofReal (Real.sqrt (gramDet (F' x)))
      ∂(μH[(m:ℝ)] : Measure (Esp_har m))) = 0 :=
    setLIntegral_measure_zero SBad _ hSBad0
  have hWint0 : (∫⁻ x in W, ENNReal.ofReal (Real.sqrt (gramDet (F' x)))
      ∂(μH[(m:ℝ)] : Measure (Esp_har m))) = 0 := by
    rw [hWdef, lintegral_union hZmeas hDisjointBZ, hSBadint0, hZdeg0, add_zero]
  have hintEq : (∫⁻ x in S, ENNReal.ofReal (Real.sqrt (gramDet (F' x)))
      ∂(μH[(m:ℝ)] : Measure (Esp_har m)))
      = ∫⁻ x in SPlus, ENNReal.ofReal (Real.sqrt (gramDet (F' x)))
          ∂(μH[(m:ℝ)] : Measure (Esp_har m)) := by
    rw [hpart, lintegral_union hWmeas hDisjointSW, hWint0, add_zero]
  rw [hmeasEq, hintEq]
  exact hmain

end RobinCaps.Hausdorff
end
