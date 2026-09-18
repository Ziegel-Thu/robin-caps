import Mathlib
import RobinCaps.Sobolev.Weak
import RobinCaps.Cap.Basic

/-!
# U-SOB-P: the weak-`H¹` layer on the product ambient space `CapSpace m`

This file ports `RobinCaps/Sobolev/Weak.lean` from `EuclideanSpace ℝ (Fin n)` to the **product**
ambient space of the thin domain,

`P := CapSpace m = ℝ × EuclideanSpace ℝ (Fin m)`,

which is the type already used by `RobinCaps.Cap.*`.

## Why a separate layer and not a reuse of `Weak.HasWeakGrad`

`Prod.norm_def` says that `ℝ × EuclideanSpace ℝ (Fin m)` carries the **sup norm**.  Therefore
`‖fderiv ℝ u p‖` is the operator norm of `fderiv ℝ u p` for the sup norm, i.e. the dual
`ℓ¹`-type quantity `|∂ₓu| + ‖∇_z u‖`, **not** `√((∂ₓu)² + ‖∇_zu‖²)`.  Writing the Dirichlet
energy as `∫ ‖fderiv ℝ u p‖ ^ 2` on `CapSpace m` would formalise the *wrong* functional.  The
axial and the transverse derivative are therefore kept **separate** throughout, and the
Dirichlet integrand is spelled out as

`(∂ₓ u)² + ‖∇_z u‖²`.

## Contents

* `HasWeakGradP Ω u gx gz`: the pair `(gx, gz)` is a weak gradient of `u` on the open set `Ω`,
  i.e. `∫_Ω u ∂ₓφ = -∫_Ω gx φ` and `∫_Ω u ∂_{z i}φ = -∫_Ω (gz)ᵢ φ` for every test function `φ`.
  Here `∂ₓφ p = fderiv ℝ φ p (1, 0)` and `∂_{z i}φ p = fderiv ℝ φ p (0, EuclideanSpace.single i 1)`.
* `H1P Ω`: a function together with a chosen axial and transverse weak derivative, all three
  square integrable on `Ω`; `AddCommGroup`/`Module ℝ` by pullback along
  `u ↦ (u.toFun, u.gx, u.gz)`.
* The forms `massP`, `dirichletP`, their nonnegativity and a.e.-invariance, the bilinear versions
  `massBilinP`, `dirichletBilinP` (diagonal = the quadratic forms) and their bundled forms
  `massBilinPₗ`, `dirichletBilinPₗ : H1P Ω →ₗ[ℝ] H1P Ω →ₗ[ℝ] ℝ`.
* `HasWeakGradP.ae_eq_gx`, `HasWeakGradP.ae_eq_gz`: **uniqueness of the weak gradient** a.e. on
  an open `Ω`, from `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` (which holds on every
  finite-dimensional real normed space, hence on `CapSpace m`, for an arbitrary measure).
* `HasWeakGradP.mono`: localisation along `Ω' ⊆ Ω`.
* `hasWeakGradP_classical`: a `C¹` function has `(dxP u, gradZP u)` as a weak gradient on every
  set.  This is proved by Fubini (`Measure.volume_eq_prod` is `rfl` on the product): the axial
  direction reduces to the one-dimensional fundamental theorem of calculus, and the transverse
  direction reduces to the already proved `Weak.integral_fderiv_single_eq_zero` on
  `EuclideanSpace ℝ (Fin m)`.  Consequently `H1P.ofCompactSupport`.
* `SliceACL`, `SliceACLAxial`: the two structural slice statements needed later by the trace
  argument, recorded as `Prop`-valued `def` **targets** (statements only, not proved).

Everything except the two final targets is proved without `sorry`, `axiom` or `admit`.
-/

open MeasureTheory Set Filter

open scoped ContDiff ENNReal Topology

namespace RobinCaps.ThinDomain

noncomputable section

variable {m : ℕ}

/-! ### The weak gradient on the product -/

/-- **Weak gradient on the product space.**  `(gx, gz)` is a weak gradient of `u` on
`Ω ⊆ CapSpace m` if for every test function `φ` (smooth, compactly supported, `tsupport φ ⊆ Ω`)

`∫_Ω u · ∂ₓφ = - ∫_Ω gx · φ`  and  `∫_Ω u · ∂_{zᵢ}φ = - ∫_Ω (gz)ᵢ · φ`  for all `i`,

where `∂ₓφ p = fderiv ℝ φ p (1, 0)` and `∂_{zᵢ}φ p = fderiv ℝ φ p (0, EuclideanSpace.single i 1)`.
The two families of directions are kept separate on purpose: the product carries the sup norm,
so the Euclidean length of `fderiv ℝ u p` is *not* the Dirichlet integrand. -/
def HasWeakGradP (Ω : Set (CapSpace m)) (u : CapSpace m → ℝ) (gx : CapSpace m → ℝ)
    (gz : CapSpace m → EuclideanSpace ℝ (Fin m)) : Prop :=
  ∀ φ : CapSpace m → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    (∫ p in Ω, u p * fderiv ℝ φ p (1, 0) = - ∫ p in Ω, gx p * φ p) ∧
    (∀ i : Fin m, ∫ p in Ω, u p * fderiv ℝ φ p (0, EuclideanSpace.single i 1)
      = - ∫ p in Ω, gz p i * φ p)

/-! ### Integrability of the pairings -/

section Integrability

variable {μ : Measure (CapSpace m)}

/-- A smooth compactly supported function is in `L²(μ)`. -/
theorem memLp_two_of_testP [IsFiniteMeasureOnCompacts μ] {φ : CapSpace m → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) : MemLp φ 2 μ :=
  hφ.continuous.memLp_of_hasCompactSupport hφc

/-- The directional derivative `p ↦ fderiv ℝ φ p v` of a smooth compactly supported function is
in `L²(μ)`, for every direction `v`. -/
theorem memLp_two_dirDeriv [IsFiniteMeasureOnCompacts μ] {φ : CapSpace m → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (v : CapSpace m) :
    MemLp (fun p => fderiv ℝ φ p v) 2 μ := by
  have hc : Continuous fun p : CapSpace m => fderiv ℝ φ p v :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  exact hc.memLp_of_hasCompactSupport (hφc.fderiv_apply ℝ v)

/-- `u ∈ L²` times a directional derivative of a test function is integrable. -/
theorem integrable_mul_dirDeriv [IsFiniteMeasureOnCompacts μ] {u : CapSpace m → ℝ}
    (hu : MemLp u 2 μ) {φ : CapSpace m → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (v : CapSpace m) : Integrable (fun p => u p * fderiv ℝ φ p v) μ :=
  hu.integrable_mul (memLp_two_dirDeriv hφ hφc v)

/-- The `i`-th component of an `L²` transverse vector field is in `L²`. -/
theorem memLp_two_compP {g : CapSpace m → EuclideanSpace ℝ (Fin m)} (hg : MemLp g 2 μ)
    (i : Fin m) : MemLp (fun p => g p i) 2 μ := by
  have h := (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ).comp_memLp' hg
  simpa [Function.comp_def] using h

/-- `(gz)ᵢ ∈ L²` times a test function is integrable. -/
theorem integrable_compP_mul [IsFiniteMeasureOnCompacts μ]
    {g : CapSpace m → EuclideanSpace ℝ (Fin m)} (hg : MemLp g 2 μ) {φ : CapSpace m → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (i : Fin m) :
    Integrable (fun p => g p i * φ p) μ :=
  (memLp_two_compP hg i).integrable_mul (memLp_two_of_testP hφ hφc)

/-- `gx ∈ L²` times a test function is integrable. -/
theorem integrable_gx_mul [IsFiniteMeasureOnCompacts μ] {g : CapSpace m → ℝ} (hg : MemLp g 2 μ)
    {φ : CapSpace m → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    Integrable (fun p => g p * φ p) μ :=
  hg.integrable_mul (memLp_two_of_testP hφ hφc)

end Integrability

/-! ### Algebra of weak gradients -/

namespace HasWeakGradP

variable {Ω : Set (CapSpace m)}

/-- The zero function has weak gradient `0`. -/
theorem zero : HasWeakGradP Ω (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
    (fun _ => (0 : EuclideanSpace ℝ (Fin m))) := by
  intro φ _ _ _
  refine ⟨by simp, fun i => by simp⟩

/-- Weak gradients add. -/
theorem add {u v : CapSpace m → ℝ} {gx hx : CapSpace m → ℝ}
    {gz hz : CapSpace m → EuclideanSpace ℝ (Fin m)}
    (hu : MemLp u 2 (volume.restrict Ω)) (hv : MemLp v 2 (volume.restrict Ω))
    (hgx : MemLp gx 2 (volume.restrict Ω)) (hhx : MemLp hx 2 (volume.restrict Ω))
    (hgz : MemLp gz 2 (volume.restrict Ω)) (hhz : MemLp hz 2 (volume.restrict Ω))
    (h1 : HasWeakGradP Ω u gx gz) (h2 : HasWeakGradP Ω v hx hz) :
    HasWeakGradP Ω (u + v) (gx + hx) (gz + hz) := by
  intro φ hφ hφc hφs
  obtain ⟨e1, f1⟩ := h1 φ hφ hφc hφs
  obtain ⟨e2, f2⟩ := h2 φ hφ hφc hφs
  constructor
  · have hL : (∫ p in Ω, (u + v) p * fderiv ℝ φ p (1, 0))
        = (∫ p in Ω, u p * fderiv ℝ φ p (1, 0)) + ∫ p in Ω, v p * fderiv ℝ φ p (1, 0) := by
      rw [← integral_add (integrable_mul_dirDeriv hu hφ hφc _)
        (integrable_mul_dirDeriv hv hφ hφc _)]
      exact integral_congr_ae (.of_forall fun p => by simp only [Pi.add_apply]; ring)
    have hR : (∫ p in Ω, (gx + hx) p * φ p)
        = (∫ p in Ω, gx p * φ p) + ∫ p in Ω, hx p * φ p := by
      rw [← integral_add (integrable_gx_mul hgx hφ hφc) (integrable_gx_mul hhx hφ hφc)]
      exact integral_congr_ae (.of_forall fun p => by simp only [Pi.add_apply]; ring)
    rw [hL, hR, e1, e2]; ring
  · intro i
    have hL : (∫ p in Ω, (u + v) p * fderiv ℝ φ p (0, EuclideanSpace.single i 1))
        = (∫ p in Ω, u p * fderiv ℝ φ p (0, EuclideanSpace.single i 1))
          + ∫ p in Ω, v p * fderiv ℝ φ p (0, EuclideanSpace.single i 1) := by
      rw [← integral_add (integrable_mul_dirDeriv hu hφ hφc _)
        (integrable_mul_dirDeriv hv hφ hφc _)]
      exact integral_congr_ae (.of_forall fun p => by simp only [Pi.add_apply]; ring)
    have hR : (∫ p in Ω, (gz + hz) p i * φ p)
        = (∫ p in Ω, gz p i * φ p) + ∫ p in Ω, hz p i * φ p := by
      rw [← integral_add (integrable_compP_mul hgz hφ hφc i) (integrable_compP_mul hhz hφ hφc i)]
      exact integral_congr_ae (.of_forall fun p => by
        simp only [Pi.add_apply, PiLp.add_apply]; ring)
    rw [hL, hR, f1 i, f2 i]; ring

/-- Weak gradients are compatible with real scalar multiplication. -/
theorem smul (c : ℝ) {u gx : CapSpace m → ℝ} {gz : CapSpace m → EuclideanSpace ℝ (Fin m)}
    (h : HasWeakGradP Ω u gx gz) : HasWeakGradP Ω (c • u) (c • gx) (c • gz) := by
  intro φ hφ hφc hφs
  obtain ⟨e1, f1⟩ := h φ hφ hφc hφs
  constructor
  · have hL : (∫ p in Ω, (c • u) p * fderiv ℝ φ p (1, 0))
        = c * ∫ p in Ω, u p * fderiv ℝ φ p (1, 0) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (.of_forall fun p => by
        simp only [Pi.smul_apply, smul_eq_mul]; ring)
    have hR : (∫ p in Ω, (c • gx) p * φ p) = c * ∫ p in Ω, gx p * φ p := by
      rw [← integral_const_mul]
      exact integral_congr_ae (.of_forall fun p => by
        simp only [Pi.smul_apply, smul_eq_mul]; ring)
    rw [hL, hR, e1]; ring
  · intro i
    have hL : (∫ p in Ω, (c • u) p * fderiv ℝ φ p (0, EuclideanSpace.single i 1))
        = c * ∫ p in Ω, u p * fderiv ℝ φ p (0, EuclideanSpace.single i 1) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (.of_forall fun p => by
        simp only [Pi.smul_apply, smul_eq_mul]; ring)
    have hR : (∫ p in Ω, (c • gz) p i * φ p) = c * ∫ p in Ω, gz p i * φ p := by
      rw [← integral_const_mul]
      exact integral_congr_ae (.of_forall fun p => by
        simp only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]; ring)
    rw [hL, hR, f1 i]; ring

/-- The weak-gradient relation only depends on the a.e.-classes on `Ω`. -/
theorem congr_ae {u u' gx gx' : CapSpace m → ℝ}
    {gz gz' : CapSpace m → EuclideanSpace ℝ (Fin m)}
    (hu : u =ᵐ[volume.restrict Ω] u') (hx : gx =ᵐ[volume.restrict Ω] gx')
    (hz : gz =ᵐ[volume.restrict Ω] gz') (h : HasWeakGradP Ω u gx gz) :
    HasWeakGradP Ω u' gx' gz' := by
  intro φ hφ hφc hφs
  obtain ⟨e1, f1⟩ := h φ hφ hφc hφs
  refine ⟨?_, fun i => ?_⟩
  · have hL : (∫ p in Ω, u' p * fderiv ℝ φ p (1, 0))
        = ∫ p in Ω, u p * fderiv ℝ φ p (1, 0) := by
      refine integral_congr_ae ?_
      filter_upwards [hu] with p hp; rw [hp]
    have hR : (∫ p in Ω, gx' p * φ p) = ∫ p in Ω, gx p * φ p := by
      refine integral_congr_ae ?_
      filter_upwards [hx] with p hp; rw [hp]
    rw [hL, hR, e1]
  · have hL : (∫ p in Ω, u' p * fderiv ℝ φ p (0, EuclideanSpace.single i 1))
        = ∫ p in Ω, u p * fderiv ℝ φ p (0, EuclideanSpace.single i 1) := by
      refine integral_congr_ae ?_
      filter_upwards [hu] with p hp; rw [hp]
    have hR : (∫ p in Ω, gz' p i * φ p) = ∫ p in Ω, gz p i * φ p := by
      refine integral_congr_ae ?_
      filter_upwards [hz] with p hp; rw [hp]
    rw [hL, hR, f1 i]

/-- A test function supported in `S` only sees `S`: for `tsupport φ ⊆ S` the integral of
`u · ∂_vφ` over `S` is the integral over the whole space. -/
theorem setIntegral_mul_dirDeriv_eq_integral {u : CapSpace m → ℝ} {φ : CapSpace m → ℝ}
    (v : CapSpace m) {S : Set (CapSpace m)} (hS : tsupport φ ⊆ S) :
    (∫ p in S, u p * fderiv ℝ φ p v) = ∫ p, u p * fderiv ℝ φ p v := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  have hps : p ∉ tsupport φ := fun h => hp (hS h)
  have hd : fderiv ℝ φ p = 0 :=
    Function.notMem_support.1 fun h => hps (support_fderiv_subset ℝ h)
  rw [hd]; simp

/-- The companion statement for a right-hand pairing `g · φ`. -/
theorem setIntegral_mul_eq_integral {g : CapSpace m → ℝ} {φ : CapSpace m → ℝ}
    {S : Set (CapSpace m)} (hS : tsupport φ ⊆ S) :
    (∫ p in S, g p * φ p) = ∫ p, g p * φ p := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  rw [image_eq_zero_of_notMem_tsupport fun h => hp (hS h)]
  simp

/-- **Locality of weak gradients.**  A weak gradient on `Ω` restricts to a weak gradient on every
subset `Ω' ⊆ Ω`. -/
theorem mono {Ω Ω' : Set (CapSpace m)} (hsub : Ω' ⊆ Ω) {u gx : CapSpace m → ℝ}
    {gz : CapSpace m → EuclideanSpace ℝ (Fin m)} (h : HasWeakGradP Ω u gx gz) :
    HasWeakGradP Ω' u gx gz := by
  intro φ hφ hφc hφs
  have hφsΩ : tsupport φ ⊆ Ω := hφs.trans hsub
  obtain ⟨e1, f1⟩ := h φ hφ hφc hφsΩ
  refine ⟨?_, fun i => ?_⟩
  · rw [setIntegral_mul_dirDeriv_eq_integral (u := u) _ hφs,
      setIntegral_mul_eq_integral (g := gx) hφs,
      ← setIntegral_mul_dirDeriv_eq_integral (u := u) _ hφsΩ,
      ← setIntegral_mul_eq_integral (g := gx) hφsΩ]
    exact e1
  · rw [setIntegral_mul_dirDeriv_eq_integral (u := u) _ hφs,
      setIntegral_mul_eq_integral (g := fun p => gz p i) hφs,
      ← setIntegral_mul_dirDeriv_eq_integral (u := u) _ hφsΩ,
      ← setIntegral_mul_eq_integral (g := fun p => gz p i) hφsΩ]
    exact f1 i

end HasWeakGradP

/-! ### Uniqueness of the weak gradient -/

/-- **Uniqueness of the axial weak derivative.**  Two `L²` axial weak derivatives of the same
function on an open set agree a.e.  Proved from the fundamental lemma of the calculus of
variations `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`, which is available on every
finite-dimensional real normed space — in particular on `CapSpace m` — for an arbitrary
measure. -/
theorem HasWeakGradP.ae_eq_gx {Ω : Set (CapSpace m)} (hΩ : IsOpen Ω) {u gx gx' : CapSpace m → ℝ}
    {gz gz' : CapSpace m → EuclideanSpace ℝ (Fin m)}
    (hgx : MemLp gx 2 (volume.restrict Ω)) (hgx' : MemLp gx' 2 (volume.restrict Ω))
    (h : HasWeakGradP Ω u gx gz) (h' : HasWeakGradP Ω u gx' gz') :
    gx =ᵐ[volume.restrict Ω] gx' := by
  have hloc : LocallyIntegrableOn (fun p => gx p - gx' p) Ω (volume.restrict Ω) := by
    have hmem : MemLp (fun p => gx p - gx' p) 2 (volume.restrict Ω) := hgx.sub hgx'
    exact (hmem.locallyIntegrable (by norm_num)).locallyIntegrableOn Ω
  have hvan : ∀ᵐ p ∂(volume.restrict Ω), p ∈ Ω → gx p - gx' p = 0 := by
    refine hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc ?_
    intro φ hφ hφc hφs
    obtain ⟨e1, _⟩ := h φ hφ hφc hφs
    obtain ⟨e2, _⟩ := h' φ hφ hφc hφs
    have hsplit : (∫ p, φ p • (gx p - gx' p) ∂(volume.restrict Ω))
        = (∫ p in Ω, gx p * φ p) - ∫ p in Ω, gx' p * φ p := by
      rw [← integral_sub (integrable_gx_mul hgx hφ hφc) (integrable_gx_mul hgx' hφ hφc)]
      exact integral_congr_ae (.of_forall fun p => by simp only [smul_eq_mul]; ring)
    rw [hsplit]
    linarith [e1, e2]
  filter_upwards [hvan, ae_restrict_mem hΩ.measurableSet] with p hp hpΩ
  exact sub_eq_zero.1 (hp hpΩ)

/-- **Uniqueness of the transverse weak gradient.** -/
theorem HasWeakGradP.ae_eq_gz {Ω : Set (CapSpace m)} (hΩ : IsOpen Ω) {u gx gx' : CapSpace m → ℝ}
    {gz gz' : CapSpace m → EuclideanSpace ℝ (Fin m)}
    (hgz : MemLp gz 2 (volume.restrict Ω)) (hgz' : MemLp gz' 2 (volume.restrict Ω))
    (h : HasWeakGradP Ω u gx gz) (h' : HasWeakGradP Ω u gx' gz') :
    gz =ᵐ[volume.restrict Ω] gz' := by
  have hcoord : ∀ i : Fin m, ∀ᵐ p ∂(volume.restrict Ω), p ∈ Ω → gz p i - gz' p i = 0 := by
    intro i
    have hloc : LocallyIntegrableOn (fun p => gz p i - gz' p i) Ω (volume.restrict Ω) := by
      have hmem : MemLp (fun p => gz p i - gz' p i) 2 (volume.restrict Ω) :=
        (memLp_two_compP hgz i).sub (memLp_two_compP hgz' i)
      exact (hmem.locallyIntegrable (by norm_num)).locallyIntegrableOn Ω
    refine hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc ?_
    intro φ hφ hφc hφs
    obtain ⟨_, f1⟩ := h φ hφ hφc hφs
    obtain ⟨_, f2⟩ := h' φ hφ hφc hφs
    have hsplit : (∫ p, φ p • (gz p i - gz' p i) ∂(volume.restrict Ω))
        = (∫ p in Ω, gz p i * φ p) - ∫ p in Ω, gz' p i * φ p := by
      rw [← integral_sub (integrable_compP_mul hgz hφ hφc i)
        (integrable_compP_mul hgz' hφ hφc i)]
      exact integral_congr_ae (.of_forall fun p => by simp only [smul_eq_mul]; ring)
    rw [hsplit]
    linarith [f1 i, f2 i]
  have hall : ∀ᵐ p ∂(volume.restrict Ω), ∀ i : Fin m, p ∈ Ω → gz p i - gz' p i = 0 :=
    ae_all_iff.2 hcoord
  filter_upwards [hall, ae_restrict_mem hΩ.measurableSet] with p hp hpΩ
  ext i
  exact sub_eq_zero.1 (hp i hpΩ)

/-! ### The weak Sobolev space `H¹(Ω)` on the product -/

/-- **The weak Sobolev layer `H¹(Ω)` on `CapSpace m`.**

An element is a function together with a chosen *axial* weak derivative `gx` and a chosen
*transverse* weak gradient `gz`, all square integrable on `Ω`.  Equality of elements is equality
of the triple of representatives. -/
structure H1P (Ω : Set (CapSpace m)) where
  /-- The underlying function. -/
  toFun : CapSpace m → ℝ
  /-- The chosen axial weak derivative `∂ₓu`. -/
  gx : CapSpace m → ℝ
  /-- The chosen transverse weak gradient `∇_z u`. -/
  gz : CapSpace m → EuclideanSpace ℝ (Fin m)
  /-- `toFun ∈ L²(Ω)`. -/
  memL2 : MemLp toFun 2 (volume.restrict Ω)
  /-- `gx ∈ L²(Ω)`. -/
  gx_memL2 : MemLp gx 2 (volume.restrict Ω)
  /-- `gz ∈ L²(Ω; ℝᵐ)`. -/
  gz_memL2 : MemLp gz 2 (volume.restrict Ω)
  /-- `(gx, gz)` is a weak gradient of `toFun` on `Ω`. -/
  hasWeakGrad : HasWeakGradP Ω toFun gx gz

namespace H1P

variable {Ω : Set (CapSpace m)}

/-- The triple of representatives `(u, ∂ₓu, ∇_z u)`. -/
def toTriple (u : H1P Ω) :
    (CapSpace m → ℝ) × (CapSpace m → ℝ) × (CapSpace m → EuclideanSpace ℝ (Fin m)) :=
  (u.toFun, u.gx, u.gz)

@[ext]
theorem ext {u v : H1P Ω} (h₁ : u.toFun = v.toFun) (h₂ : u.gx = v.gx) (h₃ : u.gz = v.gz) :
    u = v := by
  cases u; cases v; simp_all

theorem toTriple_injective : Function.Injective (toTriple : H1P Ω → _) := by
  intro u v h
  exact H1P.ext (congrArg Prod.fst h) (congrArg (Prod.fst ∘ Prod.snd) h)
    (congrArg (Prod.snd ∘ Prod.snd) h)

/-- The zero element. -/
def zero : H1P Ω where
  toFun := fun _ => 0
  gx := fun _ => 0
  gz := fun _ => 0
  memL2 := MemLp.zero
  gx_memL2 := MemLp.zero
  gz_memL2 := MemLp.zero
  hasWeakGrad := HasWeakGradP.zero

/-- Pointwise sum. -/
def add (u v : H1P Ω) : H1P Ω where
  toFun := u.toFun + v.toFun
  gx := u.gx + v.gx
  gz := u.gz + v.gz
  memL2 := u.memL2.add v.memL2
  gx_memL2 := u.gx_memL2.add v.gx_memL2
  gz_memL2 := u.gz_memL2.add v.gz_memL2
  hasWeakGrad :=
    HasWeakGradP.add u.memL2 v.memL2 u.gx_memL2 v.gx_memL2 u.gz_memL2 v.gz_memL2
      u.hasWeakGrad v.hasWeakGrad

/-- Real scalar multiple. -/
def smul (c : ℝ) (u : H1P Ω) : H1P Ω where
  toFun := c • u.toFun
  gx := c • u.gx
  gz := c • u.gz
  memL2 := u.memL2.const_smul c
  gx_memL2 := u.gx_memL2.const_smul c
  gz_memL2 := u.gz_memL2.const_smul c
  hasWeakGrad := HasWeakGradP.smul c u.hasWeakGrad

instance instZero : Zero (H1P Ω) := ⟨H1P.zero⟩
instance instAdd : Add (H1P Ω) := ⟨H1P.add⟩
instance instSMul : SMul ℝ (H1P Ω) := ⟨H1P.smul⟩
instance instSMulNat : SMul ℕ (H1P Ω) := ⟨fun k u => (k : ℝ) • u⟩

@[simp] theorem zero_toFun : (0 : H1P Ω).toFun = fun _ => (0 : ℝ) := rfl
@[simp] theorem zero_gx : (0 : H1P Ω).gx = fun _ => (0 : ℝ) := rfl
@[simp] theorem zero_gz : (0 : H1P Ω).gz = fun _ => (0 : EuclideanSpace ℝ (Fin m)) := rfl
@[simp] theorem add_toFun (u v : H1P Ω) : (u + v).toFun = u.toFun + v.toFun := rfl
@[simp] theorem add_gx (u v : H1P Ω) : (u + v).gx = u.gx + v.gx := rfl
@[simp] theorem add_gz (u v : H1P Ω) : (u + v).gz = u.gz + v.gz := rfl
@[simp] theorem smul_toFun (c : ℝ) (u : H1P Ω) : (c • u).toFun = c • u.toFun := rfl
@[simp] theorem smul_gx (c : ℝ) (u : H1P Ω) : (c • u).gx = c • u.gx := rfl
@[simp] theorem smul_gz (c : ℝ) (u : H1P Ω) : (c • u).gz = c • u.gz := rfl

theorem toTriple_zero : toTriple (0 : H1P Ω) = 0 := rfl
theorem toTriple_add (u v : H1P Ω) : toTriple (u + v) = toTriple u + toTriple v := rfl
theorem toTriple_smul (c : ℝ) (u : H1P Ω) : toTriple (c • u) = c • toTriple u := rfl

theorem toTriple_nsmul (u : H1P Ω) (k : ℕ) : toTriple (k • u) = k • toTriple u := by
  change toTriple ((k : ℝ) • u) = k • toTriple u
  rw [toTriple_smul, Nat.cast_smul_eq_nsmul]

instance instAddCommMonoid : AddCommMonoid (H1P Ω) :=
  Function.Injective.addCommMonoid (toTriple : H1P Ω → _) toTriple_injective
    toTriple_zero toTriple_add toTriple_nsmul

instance instModule : Module ℝ (H1P Ω) :=
  Function.Injective.module ℝ
    { toFun := toTriple, map_zero' := toTriple_zero, map_add' := toTriple_add }
    toTriple_injective toTriple_smul

instance instAddCommGroup : AddCommGroup (H1P Ω) :=
  Module.addCommMonoidToAddCommGroup ℝ

end H1P

/-! ### The forms -/

/-- The `L²` mass `N_Ω[u] = ∫_Ω |u|²`. -/
def massP {Ω : Set (CapSpace m)} (u : H1P Ω) : ℝ := ∫ p in Ω, u.toFun p ^ 2

/-- **The Dirichlet energy on the product**, `∫_Ω ((∂ₓu)² + ‖∇_z u‖²)`.

The integrand is written out on purpose: `‖fderiv ℝ u p‖ ^ 2` would be the *wrong* quantity,
because `CapSpace m` carries the sup norm (`Prod.norm_def`). -/
def dirichletP {Ω : Set (CapSpace m)} (u : H1P Ω) : ℝ :=
  ∫ p in Ω, (u.gx p ^ 2 + ‖u.gz p‖ ^ 2)

theorem massP_nonneg {Ω : Set (CapSpace m)} (u : H1P Ω) : 0 ≤ massP u :=
  integral_nonneg fun _ => sq_nonneg _

theorem dirichletP_nonneg {Ω : Set (CapSpace m)} (u : H1P Ω) : 0 ≤ dirichletP u :=
  integral_nonneg fun _ => by positivity

/-- Scaling of the mass. -/
theorem massP_smul {Ω : Set (CapSpace m)} (c : ℝ) (u : H1P Ω) :
    massP (c • u) = c ^ 2 * massP u := by
  unfold massP
  rw [← integral_const_mul]
  exact integral_congr_ae (.of_forall fun p => by
    simp only [H1P.smul_toFun, Pi.smul_apply, smul_eq_mul]; ring)

/-- Scaling of the Dirichlet energy. -/
theorem dirichletP_smul {Ω : Set (CapSpace m)} (c : ℝ) (u : H1P Ω) :
    dirichletP (c • u) = c ^ 2 * dirichletP u := by
  unfold dirichletP
  rw [← integral_const_mul]
  refine integral_congr_ae (.of_forall fun p => ?_)
  simp only [H1P.smul_gx, H1P.smul_gz, Pi.smul_apply, smul_eq_mul, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  ring

/-! ### The bilinear forms -/

/-- The mass bilinear form `N(u,v) = ∫_Ω u v`. -/
def massBilinP {Ω : Set (CapSpace m)} (u v : H1P Ω) : ℝ := ∫ p in Ω, u.toFun p * v.toFun p

/-- The Dirichlet bilinear form `D(u,v) = ∫_Ω (∂ₓu ∂ₓv + ⟪∇_z u, ∇_z v⟫)`, with the transverse
inner product written out as a finite sum of products of coordinates. -/
def dirichletBilinP {Ω : Set (CapSpace m)} (u v : H1P Ω) : ℝ :=
  ∫ p in Ω, (u.gx p * v.gx p + ∑ i, u.gz p i * v.gz p i)

/-- `∑ᵢ zᵢ² = ‖z‖²` on `EuclideanSpace ℝ (Fin m)`. -/
theorem sum_mul_self_eq_norm_sq (z : EuclideanSpace ℝ (Fin m)) :
    (∑ i, z i * z i) = ‖z‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Real.norm_eq_abs, sq_abs, sq]

/-- The diagonal of the mass bilinear form is the mass. -/
theorem massBilinP_self {Ω : Set (CapSpace m)} (u : H1P Ω) : massBilinP u u = massP u := by
  unfold massBilinP massP
  exact integral_congr_ae (.of_forall fun p => (sq (u.toFun p)).symm)

/-- The diagonal of the Dirichlet bilinear form is the Dirichlet energy. -/
theorem dirichletBilinP_self {Ω : Set (CapSpace m)} (u : H1P Ω) :
    dirichletBilinP u u = dirichletP u := by
  unfold dirichletBilinP dirichletP
  refine integral_congr_ae (.of_forall fun p => ?_)
  simp only [sum_mul_self_eq_norm_sq]
  ring

/-- Symmetry of the mass bilinear form. -/
theorem massBilinP_comm {Ω : Set (CapSpace m)} (u v : H1P Ω) :
    massBilinP u v = massBilinP v u :=
  integral_congr_ae (.of_forall fun _ => mul_comm _ _)

/-- Symmetry of the Dirichlet bilinear form. -/
theorem dirichletBilinP_comm {Ω : Set (CapSpace m)} (u v : H1P Ω) :
    dirichletBilinP u v = dirichletBilinP v u :=
  integral_congr_ae (.of_forall fun p => by
    simp only [mul_comm])

section Bilinearity

variable {Ω : Set (CapSpace m)}

/-- The mass integrand of a pair of `H¹` elements is integrable. -/
theorem integrable_massIntegrand (u v : H1P Ω) :
    Integrable (fun p => u.toFun p * v.toFun p) (volume.restrict Ω) :=
  u.memL2.integrable_mul v.memL2

/-- The Dirichlet integrand of a pair of `H¹` elements is integrable. -/
theorem integrable_dirichletIntegrand (u v : H1P Ω) :
    Integrable (fun p => u.gx p * v.gx p + ∑ i, u.gz p i * v.gz p i) (volume.restrict Ω) :=
  (u.gx_memL2.integrable_mul v.gx_memL2).add
    (integrable_finset_sum _ fun i _ =>
      (memLp_two_compP u.gz_memL2 i).integrable_mul (memLp_two_compP v.gz_memL2 i))

theorem massBilinP_add_left (u v w : H1P Ω) :
    massBilinP (u + v) w = massBilinP u w + massBilinP v w := by
  unfold massBilinP
  rw [← integral_add (integrable_massIntegrand u w) (integrable_massIntegrand v w)]
  exact integral_congr_ae (.of_forall fun p => by
    simp only [H1P.add_toFun, Pi.add_apply]; ring)

theorem massBilinP_smul_left (c : ℝ) (u v : H1P Ω) :
    massBilinP (c • u) v = c * massBilinP u v := by
  unfold massBilinP
  rw [← integral_const_mul]
  exact integral_congr_ae (.of_forall fun p => by
    simp only [H1P.smul_toFun, Pi.smul_apply, smul_eq_mul]; ring)

theorem massBilinP_add_right (u v w : H1P Ω) :
    massBilinP u (v + w) = massBilinP u v + massBilinP u w := by
  rw [massBilinP_comm u (v + w), massBilinP_add_left v w u, massBilinP_comm v u,
    massBilinP_comm w u]

theorem massBilinP_smul_right (c : ℝ) (u v : H1P Ω) :
    massBilinP u (c • v) = c * massBilinP u v := by
  rw [massBilinP_comm u (c • v), massBilinP_smul_left c v u, massBilinP_comm v u]

theorem dirichletBilinP_add_left (u v w : H1P Ω) :
    dirichletBilinP (u + v) w = dirichletBilinP u w + dirichletBilinP v w := by
  unfold dirichletBilinP
  rw [← integral_add (integrable_dirichletIntegrand u w) (integrable_dirichletIntegrand v w)]
  refine integral_congr_ae (.of_forall fun p => ?_)
  simp only [H1P.add_gx, H1P.add_gz, Pi.add_apply, PiLp.add_apply, add_mul,
    Finset.sum_add_distrib]
  ring

theorem dirichletBilinP_smul_left (c : ℝ) (u v : H1P Ω) :
    dirichletBilinP (c • u) v = c * dirichletBilinP u v := by
  unfold dirichletBilinP
  rw [← integral_const_mul]
  refine integral_congr_ae (.of_forall fun p => ?_)
  simp only [H1P.smul_gx, H1P.smul_gz, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul,
    mul_assoc, ← Finset.mul_sum]
  ring

theorem dirichletBilinP_add_right (u v w : H1P Ω) :
    dirichletBilinP u (v + w) = dirichletBilinP u v + dirichletBilinP u w := by
  rw [dirichletBilinP_comm u (v + w), dirichletBilinP_add_left v w u, dirichletBilinP_comm v u,
    dirichletBilinP_comm w u]

theorem dirichletBilinP_smul_right (c : ℝ) (u v : H1P Ω) :
    dirichletBilinP u (c • v) = c * dirichletBilinP u v := by
  rw [dirichletBilinP_comm u (c • v), dirichletBilinP_smul_left c v u, dirichletBilinP_comm v u]

/-- The mass bilinear form as a bundled bilinear map `H1P Ω →ₗ[ℝ] H1P Ω →ₗ[ℝ] ℝ`. -/
def massBilinPₗ : H1P Ω →ₗ[ℝ] H1P Ω →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ massBilinP massBilinP_add_left
    (fun c u v => (massBilinP_smul_left c u v).trans (smul_eq_mul c _).symm)
    massBilinP_add_right
    (fun c u v => (massBilinP_smul_right c u v).trans (smul_eq_mul c _).symm)

@[simp] theorem massBilinPₗ_apply (u v : H1P Ω) : massBilinPₗ u v = massBilinP u v := rfl

/-- The Dirichlet bilinear form as a bundled bilinear map `H1P Ω →ₗ[ℝ] H1P Ω →ₗ[ℝ] ℝ`. -/
def dirichletBilinPₗ : H1P Ω →ₗ[ℝ] H1P Ω →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ dirichletBilinP dirichletBilinP_add_left
    (fun c u v => (dirichletBilinP_smul_left c u v).trans (smul_eq_mul c _).symm)
    dirichletBilinP_add_right
    (fun c u v => (dirichletBilinP_smul_right c u v).trans (smul_eq_mul c _).symm)

@[simp] theorem dirichletBilinPₗ_apply (u v : H1P Ω) :
    dirichletBilinPₗ u v = dirichletBilinP u v := rfl

/-- The quadratic forms are the diagonals of the bundled bilinear maps — the shape required by
`RobinCaps.Spectrum.bddAbove_ratio_of_bilinear`. -/
theorem massP_eq_massBilinPₗ (u : H1P Ω) : massP u = massBilinPₗ u u :=
  (massBilinP_self u).symm

theorem dirichletP_eq_dirichletBilinPₗ (u : H1P Ω) : dirichletP u = dirichletBilinPₗ u u :=
  (dirichletBilinP_self u).symm

end Bilinearity

/-! ### a.e.-invariance of the forms -/

/-- The mass only depends on the a.e.-class of the representative on `Ω`. -/
theorem massP_congr_ae {Ω : Set (CapSpace m)} {u v : H1P Ω}
    (h : u.toFun =ᵐ[volume.restrict Ω] v.toFun) : massP u = massP v := by
  unfold massP
  refine integral_congr_ae ?_
  filter_upwards [h] with p hp; rw [hp]

/-- The Dirichlet energy only depends on the a.e.-classes of the two weak derivatives. -/
theorem dirichletP_congr_ae {Ω : Set (CapSpace m)} {u v : H1P Ω}
    (hx : u.gx =ᵐ[volume.restrict Ω] v.gx) (hz : u.gz =ᵐ[volume.restrict Ω] v.gz) :
    dirichletP u = dirichletP v := by
  unfold dirichletP
  refine integral_congr_ae ?_
  filter_upwards [hx, hz] with p hp hq; rw [hp, hq]

/-- On an open set the chosen axial derivative is determined a.e. by the a.e.-class of the
underlying function. -/
theorem H1P.gx_ae_eq {Ω : Set (CapSpace m)} (hΩ : IsOpen Ω) {u v : H1P Ω}
    (h : u.toFun =ᵐ[volume.restrict Ω] v.toFun) : u.gx =ᵐ[volume.restrict Ω] v.gx :=
  HasWeakGradP.ae_eq_gx hΩ u.gx_memL2 v.gx_memL2 u.hasWeakGrad
    (HasWeakGradP.congr_ae h.symm (Filter.EventuallyEq.refl _ _)
      (Filter.EventuallyEq.refl _ _) v.hasWeakGrad)

/-- On an open set the chosen transverse gradient is determined a.e. by the a.e.-class of the
underlying function. -/
theorem H1P.gz_ae_eq {Ω : Set (CapSpace m)} (hΩ : IsOpen Ω) {u v : H1P Ω}
    (h : u.toFun =ᵐ[volume.restrict Ω] v.toFun) : u.gz =ᵐ[volume.restrict Ω] v.gz :=
  HasWeakGradP.ae_eq_gz hΩ u.gz_memL2 v.gz_memL2 u.hasWeakGrad
    (HasWeakGradP.congr_ae h.symm (Filter.EventuallyEq.refl _ _)
      (Filter.EventuallyEq.refl _ _) v.hasWeakGrad)

/-- **Both forms descend to a.e.-classes.**  On an open set, two elements of `H1P Ω` whose
underlying functions agree a.e. on `Ω` have the same Dirichlet energy. -/
theorem dirichletP_eq_of_toFun_ae_eq {Ω : Set (CapSpace m)} (hΩ : IsOpen Ω) {u v : H1P Ω}
    (h : u.toFun =ᵐ[volume.restrict Ω] v.toFun) : dirichletP u = dirichletP v :=
  dirichletP_congr_ae (H1P.gx_ae_eq hΩ h) (H1P.gz_ae_eq hΩ h)

/-- In particular the Dirichlet energy does not depend on the *choice* of the weak gradient. -/
theorem dirichletP_eq_of_toFun_eq {Ω : Set (CapSpace m)} (hΩ : IsOpen Ω) {u v : H1P Ω}
    (h : u.toFun = v.toFun) : dirichletP u = dirichletP v :=
  dirichletP_eq_of_toFun_ae_eq hΩ (by rw [h])

/-! ### Integration by parts on the product, and classical derivatives

`Measure.volume_eq_prod` is `rfl` on `ℝ × EuclideanSpace ℝ (Fin m)`, so the Fubini API applies
to `volume` on `CapSpace m` with no glue.  We use it twice:

* in the **axial** direction, Fubini reduces `∫ ∂ₓF = 0` to the one-dimensional fundamental
  theorem of calculus on each line `ℝ × {z}`;
* in the **transverse** direction, Fubini reduces `∫ ∂_{zᵢ}F = 0` to the already proved
  `RobinCaps.Sobolev.Weak.integral_fderiv_single_eq_zero` on each slice `{x} × ℝᵐ`.

No transport of the box divergence theorem along a measure-preserving equivalence
`CapSpace m ≃ᵐ (Fin (m+1) → ℝ)` is needed. -/

/-- The **axial** partial derivative `∂ₓu p = fderiv ℝ u p (1, 0)`. -/
def dxP (u : CapSpace m → ℝ) (p : CapSpace m) : ℝ := fderiv ℝ u p (1, 0)

/-- The **transverse** gradient `∇_z u`, the vector with components
`fderiv ℝ u p (0, EuclideanSpace.single i 1)`. -/
def gradZP (u : CapSpace m → ℝ) (p : CapSpace m) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun i => fderiv ℝ u p (0, EuclideanSpace.single i 1)

@[simp] theorem dxP_apply (u : CapSpace m → ℝ) (p : CapSpace m) :
    dxP u p = fderiv ℝ u p (1, 0) := rfl

@[simp] theorem gradZP_apply (u : CapSpace m → ℝ) (p : CapSpace m) (i : Fin m) :
    gradZP u p i = fderiv ℝ u p (0, EuclideanSpace.single i 1) := rfl

/-- **One-dimensional fundamental theorem of calculus for compactly supported functions**: if
`f : ℝ → ℝ` has the continuous derivative `f'` everywhere and compact support, then
`∫ f' = 0`. -/
theorem integral_deriv_eq_zero_of_compactSupport {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f') (hfc : HasCompactSupport f) :
    ∫ x, f' x = 0 := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hfc.isBounded
  set R : ℝ := max r 0 + 1 with hRdef
  have hrR : r < R := by
    have : r ≤ max r 0 := le_max_left _ _
    linarith
  have hR0 : 0 < R := by
    have : (0 : ℝ) ≤ max r 0 := le_max_right _ _
    linarith
  have hnot : ∀ x : ℝ, R ≤ |x| → x ∉ tsupport f := by
    intro x hx hmem
    have h1 : |x| ≤ r := by
      simpa [Real.norm_eq_abs, mem_closedBall_zero_iff] using hr hmem
    linarith
  have hderiv : f' = deriv f := funext fun x => ((hf x).deriv).symm
  have hf'0 : ∀ x : ℝ, R ≤ |x| → f' x = 0 := by
    intro x hx
    rw [hderiv]
    exact Function.notMem_support.1 fun h => hnot x hx (support_deriv_subset h)
  have hbox : (∫ x in Icc (-R) R, f' x) = ∫ x, f' x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [Set.mem_Icc] at hx
    push_neg at hx
    refine hf'0 x ?_
    rcases le_or_gt (-R) x with h | h
    · have hgt := hx h
      rw [abs_of_pos (by linarith)]
      linarith
    · rw [abs_of_neg (by linarith)]
      linarith
  rw [← hbox, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : (-R : ℝ) ≤ R),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hf x)
      (hf'.intervalIntegrable _ _)]
  have h1 : f R = 0 :=
    image_eq_zero_of_notMem_tsupport (hnot R (le_of_eq (abs_of_pos hR0).symm))
  have h2 : f (-R) = 0 :=
    image_eq_zero_of_notMem_tsupport
      (hnot (-R) (le_of_eq (by rw [abs_neg, abs_of_pos hR0] : |(-R : ℝ)| = R).symm))
  rw [h1, h2, sub_zero]

/-- The integral over `CapSpace m` of the **axial** derivative of a compactly supported `C¹`
function vanishes. -/
theorem integral_fderiv_axial_eq_zero (F : CapSpace m → ℝ) (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) : ∫ p, fderiv ℝ F p (1, 0) = 0 := by
  have hK : IsCompact (tsupport F) := hFc
  have hcont : Continuous fun p : CapSpace m => fderiv ℝ F p ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))) :=
    (hF.continuous_fderiv le_rfl).clm_apply continuous_const
  have hIntV : Integrable
      (fun p : CapSpace m => fderiv ℝ F p ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m)))) volume :=
    hcont.integrable_of_hasCompactSupport (hFc.fderiv_apply ℝ _)
  have hInt : Integrable
      (fun p : CapSpace m => fderiv ℝ F p ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))))
      ((volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin m)))) := by
    rwa [← Measure.volume_eq_prod]
  have hslice : ∀ z : EuclideanSpace ℝ (Fin m),
      (∫ x : ℝ, fderiv ℝ F (x, z) ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m)))) = 0 := by
    intro z
    have hd : ∀ x : ℝ, HasDerivAt (fun t : ℝ => F (t, z))
        (fderiv ℝ F (x, z) ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m)))) x := by
      intro x
      have h1 : HasDerivAt (fun t : ℝ => (t, z))
          ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))) x :=
        (hasDerivAt_id x).prodMk (hasDerivAt_const x z)
      have h2 := (hF.differentiable le_rfl (x, z)).hasFDerivAt.comp_hasDerivAt x h1
      simpa [Function.comp_def] using h2
    have hc : Continuous fun x : ℝ =>
        fderiv ℝ F (x, z) ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))) :=
      hcont.comp (continuous_id.prodMk continuous_const)
    have hs : HasCompactSupport fun t : ℝ => F (t, z) := by
      refine HasCompactSupport.intro (hK.image continuous_fst) ?_
      intro t ht
      exact image_eq_zero_of_notMem_tsupport fun hmem => ht ⟨(t, z), hmem, rfl⟩
    exact integral_deriv_eq_zero_of_compactSupport hd hc hs
  calc (∫ p, fderiv ℝ F p ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))))
      = ∫ p, fderiv ℝ F p ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m)))
          ∂((volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin m)))) := by
        rw [← Measure.volume_eq_prod]
    _ = ∫ z, ∫ x, fderiv ℝ F (x, z) ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))) := by
        rw [integral_prod_symm _ hInt]
    _ = 0 := by simp [hslice]

/-- The integral over `CapSpace m` of a **transverse** partial derivative of a compactly
supported `C¹` function vanishes.  Reduced by Fubini to
`RobinCaps.Sobolev.Weak.integral_fderiv_single_eq_zero` on each transverse slice. -/
theorem integral_fderiv_transverse_eq_zero (F : CapSpace m → ℝ) (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) (i : Fin m) :
    ∫ p, fderiv ℝ F p (0, EuclideanSpace.single i 1) = 0 := by
  have hK : IsCompact (tsupport F) := hFc
  have hcont : Continuous fun p : CapSpace m =>
      fderiv ℝ F p ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)) :=
    (hF.continuous_fderiv le_rfl).clm_apply continuous_const
  have hIntV : Integrable (fun p : CapSpace m =>
      fderiv ℝ F p ((0 : ℝ), EuclideanSpace.single i (1 : ℝ))) volume :=
    hcont.integrable_of_hasCompactSupport (hFc.fderiv_apply ℝ _)
  have hInt : Integrable
      (fun p : CapSpace m => fderiv ℝ F p ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)))
      ((volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin m)))) := by
    rwa [← Measure.volume_eq_prod]
  have hslice : ∀ x : ℝ,
      (∫ z : EuclideanSpace ℝ (Fin m),
        fderiv ℝ F (x, z) ((0 : ℝ), EuclideanSpace.single i (1 : ℝ))) = 0 := by
    intro x
    have hFx : ContDiff ℝ 1 fun w : EuclideanSpace ℝ (Fin m) => F (x, w) :=
      hF.comp (contDiff_const.prodMk contDiff_id)
    have hFxc : HasCompactSupport fun w : EuclideanSpace ℝ (Fin m) => F (x, w) := by
      refine HasCompactSupport.intro (hK.image continuous_snd) ?_
      intro w hw
      exact image_eq_zero_of_notMem_tsupport fun hmem => hw ⟨(x, w), hmem, rfl⟩
    have hfd : ∀ z : EuclideanSpace ℝ (Fin m),
        fderiv ℝ (fun w : EuclideanSpace ℝ (Fin m) => F (x, w)) z (EuclideanSpace.single i 1)
          = fderiv ℝ F (x, z) ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)) := by
      intro z
      have h1 : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin m) => (x, w))
          (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin m))) z :=
        hasFDerivAt_prodMk_right x z
      have h2 : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin m) => F (x, w))
          ((fderiv ℝ F (x, z)).comp
            (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin m)))) z :=
        (hF.differentiable le_rfl (x, z)).hasFDerivAt.comp z h1
      rw [h2.fderiv]
      rfl
    have h0 := RobinCaps.Sobolev.Weak.integral_fderiv_single_eq_zero
      (fun w : EuclideanSpace ℝ (Fin m) => F (x, w)) hFx hFxc i
    calc (∫ z : EuclideanSpace ℝ (Fin m),
            fderiv ℝ F (x, z) ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)))
        = ∫ z : EuclideanSpace ℝ (Fin m),
            fderiv ℝ (fun w : EuclideanSpace ℝ (Fin m) => F (x, w)) z
              (EuclideanSpace.single i 1) :=
          integral_congr_ae (.of_forall fun z => (hfd z).symm)
      _ = 0 := h0
  calc (∫ p, fderiv ℝ F p ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)))
      = ∫ p, fderiv ℝ F p ((0 : ℝ), EuclideanSpace.single i (1 : ℝ))
          ∂((volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin m)))) := by
        rw [← Measure.volume_eq_prod]
    _ = ∫ x, ∫ z, fderiv ℝ F (x, z) ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)) := by
        rw [integral_prod _ hInt]
    _ = 0 := by simp [hslice]

/-- **Integration by parts on `CapSpace m`** in a direction `v` for which the integral of the
directional derivative of a compactly supported `C¹` function is known to vanish. -/
theorem integral_mul_fderiv_eq_neg_of_dir (v : CapSpace m)
    (hz : ∀ G : CapSpace m → ℝ, ContDiff ℝ 1 G → HasCompactSupport G →
      ∫ p, fderiv ℝ G p v = 0)
    (u φ : CapSpace m → ℝ) (hu : ContDiff ℝ 1 u) (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) :
    ∫ p, u p * fderiv ℝ φ p v = - ∫ p, fderiv ℝ u p v * φ p := by
  have h0 := hz (u * φ) (hu.mul hφ) hφc.mul_left
  have hprod : ∀ p, fderiv ℝ (u * φ) p v = u p * fderiv ℝ φ p v + fderiv ℝ u p v * φ p := by
    intro p
    rw [fderiv_mul (hu.differentiable le_rfl p) (hφ.differentiable le_rfl p)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have h1 : Integrable (fun p => u p * fderiv ℝ φ p v) :=
    Continuous.integrable_of_hasCompactSupport
      (hu.continuous.mul ((hφ.continuous_fderiv le_rfl).clm_apply continuous_const))
      (hφc.fderiv_apply ℝ v).mul_left
  have h2 : Integrable (fun p => fderiv ℝ u p v * φ p) :=
    Continuous.integrable_of_hasCompactSupport
      (((hu.continuous_fderiv le_rfl).clm_apply continuous_const).mul hφ.continuous)
      hφc.mul_left
  simp only [hprod] at h0
  rw [integral_add h1 h2] at h0
  linarith [h0]

/-- **Classical derivatives are weak derivatives on the product.**  For every `C¹` function `u`
and every set `Ω`, the pair `(∂ₓu, ∇_z u)` is a weak gradient of `u` on `Ω`. -/
theorem hasWeakGradP_classical (Ω : Set (CapSpace m)) (u : CapSpace m → ℝ)
    (hu : ContDiff ℝ 1 u) : HasWeakGradP Ω u (dxP u) (gradZP u) := by
  intro φ hφ hφc hφs
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  refine ⟨?_, fun i => ?_⟩
  · rw [HasWeakGradP.setIntegral_mul_dirDeriv_eq_integral (u := u) _ hφs,
      HasWeakGradP.setIntegral_mul_eq_integral (g := dxP u) hφs]
    exact integral_mul_fderiv_eq_neg_of_dir _
      (fun G hG hGc => integral_fderiv_axial_eq_zero G hG hGc) u φ hu hφ1 hφc
  · rw [HasWeakGradP.setIntegral_mul_dirDeriv_eq_integral (u := u) _ hφs,
      HasWeakGradP.setIntegral_mul_eq_integral (g := fun p => gradZP u p i) hφs]
    exact integral_mul_fderiv_eq_neg_of_dir _
      (fun G hG hGc => integral_fderiv_transverse_eq_zero G hG hGc i) u φ hu hφ1 hφc

/-- The axial derivative of a `C¹` function is continuous. -/
theorem continuous_dxP (u : CapSpace m → ℝ) (hu : ContDiff ℝ 1 u) : Continuous (dxP u) :=
  (hu.continuous_fderiv le_rfl).clm_apply continuous_const

/-- The transverse gradient of a `C¹` function is continuous. -/
theorem continuous_gradZP (u : CapSpace m → ℝ) (hu : ContDiff ℝ 1 u) :
    Continuous (gradZP u) := by
  have hL : Continuous (WithLp.toLp 2 : (Fin m → ℝ) → EuclideanSpace ℝ (Fin m)) :=
    (EuclideanSpace.equiv (Fin m) ℝ).symm.continuous
  exact hL.comp (continuous_pi fun i =>
    (hu.continuous_fderiv le_rfl).clm_apply continuous_const)

/-- The axial derivative of a compactly supported function has compact support. -/
theorem hasCompactSupport_dxP (u : CapSpace m → ℝ) (huc : HasCompactSupport u) :
    HasCompactSupport (dxP u) := huc.fderiv_apply ℝ _

/-- The transverse gradient of a compactly supported function has compact support. -/
theorem hasCompactSupport_gradZP (u : CapSpace m → ℝ) (huc : HasCompactSupport u) :
    HasCompactSupport (gradZP u) :=
  (huc.fderiv ℝ).comp_left
    (g := fun L : CapSpace m →L[ℝ] ℝ =>
      (WithLp.toLp 2 fun i => L (0, EuclideanSpace.single i 1) : EuclideanSpace ℝ (Fin m)))
    (by ext i; simp)

/-- **A `C¹` function with compact support is an element of `H1P Ω`**, with its classical axial
and transverse derivatives as weak derivatives (for any set `Ω`). -/
def H1P.ofCompactSupport (Ω : Set (CapSpace m)) (u : CapSpace m → ℝ) (hu : ContDiff ℝ 1 u)
    (huc : HasCompactSupport u) : H1P Ω where
  toFun := u
  gx := dxP u
  gz := gradZP u
  memL2 := hu.continuous.memLp_of_hasCompactSupport huc
  gx_memL2 := (continuous_dxP u hu).memLp_of_hasCompactSupport (hasCompactSupport_dxP u huc)
  gz_memL2 := (continuous_gradZP u hu).memLp_of_hasCompactSupport (hasCompactSupport_gradZP u huc)
  hasWeakGrad := hasWeakGradP_classical Ω u hu

@[simp] theorem H1P.ofCompactSupport_toFun (Ω : Set (CapSpace m)) (u : CapSpace m → ℝ)
    (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) :
    (H1P.ofCompactSupport Ω u hu huc).toFun = u := rfl

@[simp] theorem H1P.ofCompactSupport_gx (Ω : Set (CapSpace m)) (u : CapSpace m → ℝ)
    (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) :
    (H1P.ofCompactSupport Ω u hu huc).gx = dxP u := rfl

@[simp] theorem H1P.ofCompactSupport_gz (Ω : Set (CapSpace m)) (u : CapSpace m → ℝ)
    (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) :
    (H1P.ofCompactSupport Ω u hu huc).gz = gradZP u := rfl

/-! ### Targets: the slice statements needed by the trace argument

The following two are **statements only** (`Prop`-valued `def`s).  They are not proved here and
none of them is used as a hypothesis anywhere above; nothing in this file depends on them.  They
are the "absolutely continuous on lines" facts that the slice-wise trace argument of the thin
domain will need. -/

/-- **Target (transverse slices).**  For almost every axial coordinate `x`, the transverse slice
`z ↦ u(x, z)` has `z ↦ (∇_z u)(x, z)` as a weak gradient — in the sense of
`RobinCaps.Sobolev.Weak.HasWeakGrad` on `EuclideanSpace ℝ (Fin m)` — on the open transverse
slice `Ω_x = {z | (x, z) ∈ Ω}`.

This is the multi-dimensional "absolutely continuous on lines" (ACL) property in the transverse
variable.  It is what lets the trace be computed slice by slice against the radial
one-dimensional trace inequality of `RobinCaps/Sobolev/Interval.lean`. -/
def SliceACL (Ω : Set (CapSpace m)) (u : H1P Ω) : Prop :=
  ∀ᵐ x : ℝ, RobinCaps.Sobolev.Weak.HasWeakGrad {z : EuclideanSpace ℝ (Fin m) | (x, z) ∈ Ω}
    (fun z => u.toFun (x, z)) (fun z => u.gz (x, z))

/-- **Target (axial slices).**  For almost every transverse coordinate `z`, the axial slice
`x ↦ u(x, z)` has `x ↦ (∂ₓu)(x, z)` as a weak derivative on the open axial slice
`Ω^z = {x | (x, z) ∈ Ω} ⊆ ℝ`.

This is the axial analogue of `SliceACL`; the one-dimensional weak-derivative condition is
spelled out because `RobinCaps.Sobolev.Weak.HasWeakGrad` lives on `EuclideanSpace ℝ (Fin n)`
and the axial slice is a subset of `ℝ`. -/
def SliceACLAxial (Ω : Set (CapSpace m)) (u : H1P Ω) : Prop :=
  ∀ᵐ z : EuclideanSpace ℝ (Fin m), ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    tsupport φ ⊆ {x : ℝ | (x, z) ∈ Ω} →
      ∫ x in {x : ℝ | (x, z) ∈ Ω}, u.toFun (x, z) * deriv φ x
        = - ∫ x in {x : ℝ | (x, z) ∈ Ω}, u.gx (x, z) * φ x

end

end RobinCaps.ThinDomain

