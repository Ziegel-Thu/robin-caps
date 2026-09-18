import Mathlib
import RobinCaps.ThinDomain.H1P
import RobinCaps.Domain.Thin
import RobinCaps.Domain.ThinConvex
import RobinCaps.Domain.ThinDiam
import RobinCaps.Domain.CapsuleThin
import RobinCaps.Compact.Dilation
import RobinCaps.Compact.Contraction
import RobinCaps.Compact.L2Approx
import RobinCaps.Compact.H1Limit
import RobinCaps.ThinDomain.H1PQuotient
import RobinCaps.ThinDomain.BulkEnergy

/-!
# Density of `C¹` functions in `H¹` of the thin domain

**Main theorem**: `exists_c1_h1_close_cd` — every `u ∈ H1P (thinDomain Cm Cp L R)` is the
`H¹`-limit (jointly in mass and Dirichlet energy) of functions `v` that are `C¹` on all of
`CapSpace m`, hence continuous up to the boundary
(`continuousOn_closure_of_exists_c1_h1_close_cd`).

## Route taken: transport (Route A)

`CapSpace m = ℝ × EuclideanSpace ℝ (Fin m)` carries the *sup* norm, so it is not itself an inner
product space and none of `RobinCaps/Compact/*` applies to it directly. Instead we transport
along the linear identification `toEuclid m : CapSpace m ≃ EuclideanSpace ℝ (Fin (m+1))` of
`RobinCaps/Domain/CapsuleThin.lean` (`capSpaceCLE_cd`, a continuous linear equivalence built here),
under which:

* the axial/transverse directions `(1,0)`, `(0, eᵢ)` correspond exactly to the standard basis
  of `EuclideanSpace ℝ (Fin (m+1))` (`toEuclid_axial_cd`, `toEuclid_transverse_cd`), so
  `HasWeakGradP` transports to `RobinCaps.Sobolev.Weak.HasWeakGrad` (`hasWeakGrad_transport_cd`,
  `transportH1P_cd`);
* `toEuclid` is measure preserving (already proved), so `massP`/`dirichletP` transport *exactly*
  (`massP_sub_ofCompactSupport_cd`, `dirichletP_sub_ofCompactSupport_cd`) — no approximation is
  lost in the transport itself.

The thin domain's Euclidean image `thinDomainE_cd Cm Cp L R` is a bounded convex open set
containing `0` (`convex_thinDomainE_cd`, `isOpen_thinDomainE_cd`, `isBounded_thinDomainE_cd`,
`zero_mem_thinDomainE_cd`), so the whole problem reduces to:

> **`exists_smooth_close_cd`**: density of `C¹` functions in `Weak.H1 Ω` for a *general* bounded
> convex open `Ω ⊆ EuclideanSpace ℝ (Fin n)` with `0 ∈ Ω`.

## The two approximation steps, generalised from balls to a general convex `Ω`

`RobinCaps/Compact/Approx.lean` proves the analogous statement only for `Ω = ball 0 R`. Since
`Ω` is star-shaped about `0` (immediate from convexity, `star_shaped_cd`), both steps generalise
with no loss of the underlying analytic content:

* **Dilation** (`dilateCd`, `exists_dilate_close_cd`): `u_λ(x) = u(λx)` is already a function on
  `Ω` itself (star-shapedness), and its closeness to `u` follows from the *global* (ball-free)
  convergence facts `RobinCaps.Compact.exists_lam_dilate_close` applied to the zero-extension of
  `u`, one coordinate of the gradient at a time.
* **Mollification** (`exists_mollify_close_cd`): the ball-specific gap `‖x‖ + δ < R` of
  `RobinCaps/Compact/WeakGradMollify.lean` is replaced by the *uniform gap* `exists_gap_cd`
  (`closure Ω ⊆ Ω_λ` for `λ < 1`, via `Convex.combo_interior_closure_mem_interior`, then
  `IsCompact.exists_thickening_subset_open`), after which the (WG) identity
  (`fderiv_conv_extCd_cd`) and the closeness (`RobinCaps.Compact.exists_delta_conv_close`)
  transcribe verbatim.

The two steps are combined via a crude `‖a+b‖² ≤ 2‖a‖² + 2‖b‖²` estimate
(`mass_le_two_add_two_cd`, `dirichlet_le_two_add_two_cd`), spending `η/4` on each of the four
resulting error terms.

No hypothesis beyond the ones in the theorem statements is left open; no `sorry`, `admit`,
`axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Metric Set Filter
open scoped Convolution ContDiff ENNReal Topology Pointwise

namespace RobinCaps.Sobolev

open RobinCaps.Cap RobinCaps.Domain RobinCaps.ThinDomain

noncomputable section

variable {m : ℕ} {Cm Cp : Cap m} {L R : ℝ}

/-- **The origin lies in the thin domain.** -/
theorem zero_mem_thinDomain_cd (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    (0 : CapSpace m) ∈ thinDomain Cm Cp L R := by
  have hL0 : 0 < L := span_pos (Cm := Cm) (Cp := Cp) hR hL
  have h0 : (0 : ℝ) ∈ Ioo (-L/2) (L/2) := by constructor <;> linarith
  simpa using axialPoint_mem_thinDomain (Cm := Cm) (Cp := Cp) hR hL h0

/-- **A convex open set containing the origin absorbs its own closure under dilation.**
For `0 ≤ λ < 1`, `λ • closure Ω ⊆ Ω`. This is the general convexity fact that replaces
`preimage_smul_ball` (ball-specific) in the argument of `RobinCaps/Compact/Dilation.lean`. -/
theorem smul_closure_subset_cd {Ω : Set (CapSpace m)} (hconv : Convex ℝ Ω) (hopen : IsOpen Ω)
    (h0 : (0 : CapSpace m) ∈ Ω) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) :
    lam • closure Ω ⊆ Ω := by
  rintro _ ⟨y, hy, rfl⟩
  have hint : (0 : CapSpace m) ∈ interior Ω := by rwa [hopen.interior_eq]
  have hkey := hconv.combo_interior_closure_mem_interior hint hy (a := 1 - lam) (b := lam)
    (by linarith) hlam0 (by ring)
  rw [hopen.interior_eq] at hkey
  simpa using hkey

/-! ## The linear identification `CapSpace m ≃L[ℝ] EuclideanSpace ℝ (Fin (m+1))` -/

theorem toEuclid_add_cd (p q : CapSpace m) :
    toEuclid m (p + q) = toEuclid m p + toEuclid m q := by
  refine PiLp.ext fun j => ?_
  refine Fin.cases ?_ ?_ j
  · rfl
  · intro i; rfl

theorem toEuclid_zero_cd : toEuclid m (0 : CapSpace m) = 0 := by
  refine PiLp.ext fun j => ?_
  refine Fin.cases ?_ ?_ j
  · rfl
  · intro i; rfl

theorem toEuclid_smul_cd (c : ℝ) (p : CapSpace m) :
    toEuclid m (c • p) = c • toEuclid m p := by
  refine PiLp.ext fun j => ?_
  refine Fin.cases ?_ ?_ j
  · rfl
  · intro i; rfl

/-- `toEuclid` as a linear equivalence. -/
def capSpaceLinearEquiv_cd (m : ℕ) : CapSpace m ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1)) where
  toFun := toEuclid m
  invFun := ofEuclid m
  map_add' := toEuclid_add_cd
  map_smul' := toEuclid_smul_cd
  left_inv := ofEuclid_toEuclid
  right_inv := toEuclid_ofEuclid

/-- **`toEuclid` as a continuous linear equivalence.** The key transport device: `CapSpace m` and
`EuclideanSpace ℝ (Fin (m+1))` are linearly homeomorphic (though *not* isometric, since
`CapSpace m` carries the sup norm), which suffices to transport openness, convexity, boundedness
and the classical (hence weak) derivative structure. -/
def capSpaceCLE_cd (m : ℕ) : CapSpace m ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
  (capSpaceLinearEquiv_cd m).toContinuousLinearEquiv

@[simp] theorem capSpaceCLE_cd_apply (p : CapSpace m) : capSpaceCLE_cd m p = toEuclid m p := rfl

@[simp] theorem capSpaceCLE_cd_symm_apply (x : EuclideanSpace ℝ (Fin (m + 1))) :
    (capSpaceCLE_cd m).symm x = ofEuclid m x := rfl

/-! ## Transport of the geometric hypotheses to `EuclideanSpace ℝ (Fin (m+1))` -/

/-- The Euclidean image of the thin domain, on which the transported `H¹` theory of
`RobinCaps.Sobolev.Weak` and `RobinCaps.Compact` will be applied. -/
def thinDomainE_cd (Cm Cp : Cap m) (L R : ℝ) : Set (EuclideanSpace ℝ (Fin (m + 1))) :=
  toEuclid m '' thinDomain Cm Cp L R

theorem isOpen_thinDomainE_cd (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    IsOpen (thinDomainE_cd Cm Cp L R) :=
  (capSpaceCLE_cd m).toHomeomorph.isOpen_image.2 (isOpen_thinDomain hR hL)

theorem convex_thinDomainE_cd (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    Convex ℝ (thinDomainE_cd Cm Cp L R) :=
  (convex_thinDomain hR hL).linear_image (capSpaceLinearEquiv_cd m).toLinearMap

theorem isBounded_thinDomainE_cd (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    Bornology.IsBounded (thinDomainE_cd Cm Cp L R) :=
  isBounded_toEuclid_image_thinDomain hR hL

theorem zero_mem_thinDomainE_cd (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    (0 : EuclideanSpace ℝ (Fin (m + 1))) ∈ thinDomainE_cd Cm Cp L R :=
  ⟨0, zero_mem_thinDomain_cd hR hL, toEuclid_zero_cd⟩

/-! ## The chain rule along `toEuclid` / `ofEuclid` -/

/-- Chain rule for precomposition with `ofEuclid`. -/
theorem fderiv_comp_ofEuclid_cd {F : CapSpace m → ℝ} (hF : ContDiff ℝ 1 F)
    (x v : EuclideanSpace ℝ (Fin (m + 1))) :
    fderiv ℝ (F ∘ ofEuclid m) x v = fderiv ℝ F (ofEuclid m x) (ofEuclid m v) := by
  have h1 : HasFDerivAt (ofEuclid m)
      ((capSpaceCLE_cd m).symm : EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] CapSpace m) x :=
    ((capSpaceCLE_cd m).symm : EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] CapSpace m).hasFDerivAt
  have h2 : HasFDerivAt F (fderiv ℝ F (ofEuclid m x)) (ofEuclid m x) :=
    (hF.differentiable le_rfl (ofEuclid m x)).hasFDerivAt
  have h3 := h2.comp x h1
  rw [h3.fderiv]
  simp

/-- Chain rule for precomposition with `toEuclid`. -/
theorem fderiv_comp_toEuclid_cd {F : EuclideanSpace ℝ (Fin (m + 1)) → ℝ} (hF : ContDiff ℝ 1 F)
    (p w : CapSpace m) :
    fderiv ℝ (F ∘ toEuclid m) p w = fderiv ℝ F (toEuclid m p) (toEuclid m w) := by
  have h1 : HasFDerivAt (toEuclid m) ((capSpaceCLE_cd m) : CapSpace m →L[ℝ] _) p :=
    ((capSpaceCLE_cd m) : CapSpace m →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))).hasFDerivAt
  have h2 : HasFDerivAt F (fderiv ℝ F (toEuclid m p)) (toEuclid m p) :=
    (hF.differentiable le_rfl (toEuclid m p)).hasFDerivAt
  have h3 := h2.comp p h1
  rw [h3.fderiv]
  simp

theorem contDiff_comp_ofEuclid_cd {F : CapSpace m → ℝ} {n : WithTop ℕ∞} (hF : ContDiff ℝ n F) :
    ContDiff ℝ n (F ∘ ofEuclid m) :=
  hF.comp ((capSpaceCLE_cd m).symm : EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] CapSpace m).contDiff

theorem contDiff_comp_toEuclid_cd {F : EuclideanSpace ℝ (Fin (m + 1)) → ℝ} {n : WithTop ℕ∞}
    (hF : ContDiff ℝ n F) :
    ContDiff ℝ n (F ∘ toEuclid m) :=
  hF.comp ((capSpaceCLE_cd m) : CapSpace m →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))).contDiff

/-! ## Change of variables along `toEuclid` -/

/-- **Change of variables along `toEuclid`.** -/
theorem setIntegral_toEuclid_image_cd (Ω : Set (CapSpace m))
    (f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ) :
    ∫ x in toEuclid m '' Ω, f x = ∫ p in Ω, f (toEuclid m p) :=
  (measurePreserving_toEuclid m).setIntegral_image_emb
    (capSpaceMeasurableEquiv m).measurableEmbedding f Ω

/-! ## The axial and transverse directions correspond to the standard basis -/

theorem toEuclid_axial_cd : toEuclid m ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m)))
    = EuclideanSpace.single (0 : Fin (m + 1)) 1 := by
  refine PiLp.ext fun j => ?_
  refine Fin.cases ?_ ?_ j
  · simp [EuclideanSpace.single_apply]
  · intro i
    simp [EuclideanSpace.single_apply]

theorem toEuclid_transverse_cd (i : Fin m) :
    toEuclid m ((0 : ℝ), EuclideanSpace.single i 1) = EuclideanSpace.single i.succ 1 := by
  refine PiLp.ext fun j => ?_
  refine Fin.cases ?_ ?_ j
  · simp [EuclideanSpace.single_apply, (Fin.succ_ne_zero i).symm]
  · intro k
    simp [EuclideanSpace.single_apply, Fin.succ_inj]

theorem ofEuclid_axial_cd :
    ofEuclid m (EuclideanSpace.single (0 : Fin (m + 1)) 1) = ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))) := by
  rw [← toEuclid_axial_cd, ofEuclid_toEuclid]

theorem ofEuclid_transverse_cd (i : Fin m) :
    ofEuclid m (EuclideanSpace.single i.succ 1) = ((0 : ℝ), EuclideanSpace.single i 1) := by
  rw [← toEuclid_transverse_cd, ofEuclid_toEuclid]

theorem continuous_toEuclid_cd : Continuous (toEuclid m) := (capSpaceCLE_cd m).continuous
theorem continuous_ofEuclid_cd : Continuous (ofEuclid m) := (capSpaceCLE_cd m).symm.continuous

/-! ## Transport of supports along `toEuclid` / `ofEuclid` -/

theorem ofEuclid_image_eq_toEuclid_preimage_cd (S : Set (EuclideanSpace ℝ (Fin (m + 1)))) :
    ofEuclid m '' S = toEuclid m ⁻¹' S := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [mem_preimage, toEuclid_ofEuclid] using hx
  · intro hp
    exact ⟨toEuclid m p, hp, ofEuclid_toEuclid p⟩

theorem tsupport_comp_toEuclid_cd (φ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ) :
    tsupport (φ ∘ toEuclid m) = ofEuclid m '' tsupport φ := by
  have h1 : Function.support (φ ∘ toEuclid m) = toEuclid m ⁻¹' Function.support φ :=
    Function.support_comp_eq_preimage φ (toEuclid m)
  have heq : (⇑(capSpaceCLE_cd m).toHomeomorph : CapSpace m → EuclideanSpace ℝ (Fin (m + 1)))
      = toEuclid m := rfl
  show closure (Function.support (φ ∘ toEuclid m)) = _
  rw [h1, ← heq, ← (capSpaceCLE_cd m).toHomeomorph.preimage_closure, heq]
  exact (ofEuclid_image_eq_toEuclid_preimage_cd (closure (Function.support φ))).symm

theorem tsupport_comp_ofEuclid_cd (u : CapSpace m → ℝ) :
    tsupport (u ∘ ofEuclid m) = toEuclid m '' tsupport u := by
  have h1 : Function.support (u ∘ ofEuclid m) = ofEuclid m ⁻¹' Function.support u :=
    Function.support_comp_eq_preimage u (ofEuclid m)
  have heq : (⇑(capSpaceCLE_cd m).symm.toHomeomorph : EuclideanSpace ℝ (Fin (m + 1)) → CapSpace m)
      = ofEuclid m := rfl
  show closure (Function.support (u ∘ ofEuclid m)) = _
  rw [h1, ← heq, ← (capSpaceCLE_cd m).symm.toHomeomorph.preimage_closure, heq]
  exact (toEuclid_image_eq_ofEuclid_preimage (closure (Function.support u))).symm

theorem hasCompactSupport_comp_toEuclid_cd {φ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ}
    (hφc : HasCompactSupport φ) : HasCompactSupport (φ ∘ toEuclid m) := by
  rw [HasCompactSupport, tsupport_comp_toEuclid_cd]
  exact hφc.image (continuous_ofEuclid_cd)

theorem hasCompactSupport_comp_ofEuclid_cd {u : CapSpace m → ℝ}
    (huc : HasCompactSupport u) : HasCompactSupport (u ∘ ofEuclid m) := by
  rw [HasCompactSupport, tsupport_comp_ofEuclid_cd]
  exact huc.image (continuous_toEuclid_cd)

/-! ## Transport of the weak gradient -/

/-- The transported weak gradient: `g̃ x = toEuclid (gx (ofEuclid x), gz (ofEuclid x))`. -/
def gTildeCd (gx : CapSpace m → ℝ) (gz : CapSpace m → EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin (m + 1)) → EuclideanSpace ℝ (Fin (m + 1)) :=
  fun x => toEuclid m (gx (ofEuclid m x), gz (ofEuclid m x))

theorem gTildeCd_zero (gx : CapSpace m → ℝ) (gz : CapSpace m → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin (m + 1))) : gTildeCd gx gz x 0 = gx (ofEuclid m x) :=
  toEuclid_apply_zero _

theorem gTildeCd_succ (gx : CapSpace m → ℝ) (gz : CapSpace m → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin (m + 1))) (i : Fin m) :
    gTildeCd gx gz x i.succ = gz (ofEuclid m x) i :=
  toEuclid_apply_succ _ i

/-- **Transport of the weak gradient from `CapSpace m` to `EuclideanSpace ℝ (Fin (m+1))`.** -/
theorem hasWeakGrad_transport_cd {Ω : Set (CapSpace m)} {u gx : CapSpace m → ℝ}
    {gz : CapSpace m → EuclideanSpace ℝ (Fin m)} (h : HasWeakGradP Ω u gx gz) :
    RobinCaps.Sobolev.Weak.HasWeakGrad (toEuclid m '' Ω) (u ∘ ofEuclid m) (gTildeCd gx gz) := by
  intro φ hφ hφc hφs i
  set ψ : CapSpace m → ℝ := φ ∘ toEuclid m with hψdef
  have hψsmooth : ContDiff ℝ ∞ ψ := contDiff_comp_toEuclid_cd hφ
  have hψcpt : HasCompactSupport ψ := hasCompactSupport_comp_toEuclid_cd hφc
  have hφC1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  have hψsupp : tsupport ψ ⊆ Ω := by
    rw [hψdef, tsupport_comp_toEuclid_cd]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨p, hp, rfl⟩ := hφs hx
    rwa [ofEuclid_toEuclid]
  obtain ⟨e1, f1⟩ := h ψ hψsmooth hψcpt hψsupp
  refine Fin.cases ?_ (fun j => ?_) i
  · -- the axial direction, `i = 0`
    have hFL : (fun p : CapSpace m =>
        (u ∘ ofEuclid m) (toEuclid m p) * fderiv ℝ φ (toEuclid m p) (EuclideanSpace.single 0 1))
        = fun p => u p * fderiv ℝ ψ p (1, 0) := by
      funext p
      rw [Function.comp_apply, ofEuclid_toEuclid, hψdef,
        fderiv_comp_toEuclid_cd hφC1 p (1, 0), toEuclid_axial_cd]
    have hFR : (fun p : CapSpace m => gTildeCd gx gz (toEuclid m p) 0 * φ (toEuclid m p))
        = fun p => gx p * ψ p := by
      funext p
      rw [gTildeCd_zero, ofEuclid_toEuclid, hψdef, Function.comp_apply]
    rw [setIntegral_toEuclid_image_cd Ω
        (fun x => (u ∘ ofEuclid m) x * fderiv ℝ φ x (EuclideanSpace.single 0 1)),
      setIntegral_toEuclid_image_cd Ω (fun x => gTildeCd gx gz x 0 * φ x)]
    show (∫ p in Ω, (u ∘ ofEuclid m) (toEuclid m p) * fderiv ℝ φ (toEuclid m p)
        (EuclideanSpace.single 0 1)) = - ∫ p in Ω, gTildeCd gx gz (toEuclid m p) 0 * φ (toEuclid m p)
    rw [hFL, hFR]
    exact e1
  · -- a transverse direction, `i = j.succ`
    have hFL : (fun p : CapSpace m =>
        (u ∘ ofEuclid m) (toEuclid m p) * fderiv ℝ φ (toEuclid m p) (EuclideanSpace.single j.succ 1))
        = fun p => u p * fderiv ℝ ψ p (0, EuclideanSpace.single j 1) := by
      funext p
      rw [Function.comp_apply, ofEuclid_toEuclid, hψdef,
        fderiv_comp_toEuclid_cd hφC1 p (0, EuclideanSpace.single j 1), toEuclid_transverse_cd]
    have hFR : (fun p : CapSpace m => gTildeCd gx gz (toEuclid m p) j.succ * φ (toEuclid m p))
        = fun p => gz p j * ψ p := by
      funext p
      rw [gTildeCd_succ, ofEuclid_toEuclid, hψdef, Function.comp_apply]
    rw [setIntegral_toEuclid_image_cd Ω
        (fun x => (u ∘ ofEuclid m) x * fderiv ℝ φ x (EuclideanSpace.single j.succ 1)),
      setIntegral_toEuclid_image_cd Ω (fun x => gTildeCd gx gz x j.succ * φ x)]
    show (∫ p in Ω, (u ∘ ofEuclid m) (toEuclid m p) * fderiv ℝ φ (toEuclid m p)
        (EuclideanSpace.single j.succ 1))
      = - ∫ p in Ω, gTildeCd gx gz (toEuclid m p) j.succ * φ (toEuclid m p)
    rw [hFL, hFR]
    exact f1 j

/-! ## `MemLp` transport along `toEuclid` / `ofEuclid` -/

theorem measurePreserving_toEuclid_restrict_cd (Ω : Set (CapSpace m)) :
    MeasurePreserving (toEuclid m) (volume.restrict Ω) (volume.restrict (toEuclid m '' Ω)) :=
  (measurePreserving_toEuclid m).restrict_image_emb
    (capSpaceMeasurableEquiv m).measurableEmbedding Ω

theorem measurePreserving_ofEuclid_restrict_cd (Ω : Set (CapSpace m)) :
    MeasurePreserving (ofEuclid m) (volume.restrict (toEuclid m '' Ω)) (volume.restrict Ω) :=
  (measurePreserving_toEuclid_restrict_cd Ω).symm (capSpaceMeasurableEquiv m)

theorem memLp_comp_ofEuclid_cd {Ω : Set (CapSpace m)} {F : Type*} [NormedAddCommGroup F]
    {f : CapSpace m → F} {q : ℝ≥0∞} (hf : MemLp f q (volume.restrict Ω)) :
    MemLp (f ∘ ofEuclid m) q (volume.restrict (toEuclid m '' Ω)) :=
  hf.comp_measurePreserving (measurePreserving_ofEuclid_restrict_cd Ω)

theorem norm_gTildeCd_sq_cd (gx : CapSpace m → ℝ) (gz : CapSpace m → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin (m + 1))) :
    ‖gTildeCd gx gz x‖ ^ 2 = gx (ofEuclid m x) ^ 2 + ‖gz (ofEuclid m x)‖ ^ 2 := by
  simp [gTildeCd, norm_toEuclid_sq]

theorem memLp_gTildeCd_cd {Ω : Set (CapSpace m)} {gx : CapSpace m → ℝ}
    {gz : CapSpace m → EuclideanSpace ℝ (Fin m)} (hgx : MemLp gx 2 (volume.restrict Ω))
    (hgz : MemLp gz 2 (volume.restrict Ω)) :
    MemLp (gTildeCd gx gz) 2 (volume.restrict (toEuclid m '' Ω)) := by
  have hgx' := memLp_comp_ofEuclid_cd hgx
  have hgz' := memLp_comp_ofEuclid_cd hgz
  have hmeas : AEStronglyMeasurable (gTildeCd gx gz) (volume.restrict (toEuclid m '' Ω)) :=
    continuous_toEuclid_cd.comp_aestronglyMeasurable
      (hgx'.aestronglyMeasurable.prodMk hgz'.aestronglyMeasurable)
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hint : Integrable (fun x => gx (ofEuclid m x) ^ 2 + ‖gz (ofEuclid m x)‖ ^ 2)
      (volume.restrict (toEuclid m '' Ω)) :=
    ((memLp_two_iff_integrable_sq hgx'.aestronglyMeasurable).1 hgx').add
      ((memLp_two_iff_integrable_sq_norm hgz'.aestronglyMeasurable).1 hgz')
  have heq : (fun x => gx (ofEuclid m x) ^ 2 + ‖gz (ofEuclid m x)‖ ^ 2)
      = fun x => ‖gTildeCd gx gz x‖ ^ 2 := funext fun x => (norm_gTildeCd_sq_cd gx gz x).symm
  rwa [heq] at hint

/-! ## The transport `H1P Ω → Weak.H1 (toEuclid '' Ω)` -/

/-- **Transport of `H¹` elements from the thin domain to `EuclideanSpace ℝ (Fin (m+1))`.** -/
def transportH1P_cd {Ω : Set (CapSpace m)} (u : H1P Ω) :
    RobinCaps.Sobolev.Weak.H1 (toEuclid m '' Ω) where
  toFun := u.toFun ∘ ofEuclid m
  grad := gTildeCd u.gx u.gz
  memL2 := memLp_comp_ofEuclid_cd u.memL2
  grad_memL2 := memLp_gTildeCd_cd u.gx_memL2 u.gz_memL2
  hasWeakGrad := hasWeakGrad_transport_cd u.hasWeakGrad

/-! ## Difference formulas -/

theorem massP_sub_cd {Ω : Set (CapSpace m)} (u v : H1P Ω) :
    massP (u - v) = ∫ p in Ω, (u.toFun p - v.toFun p) ^ 2 := by
  unfold massP; rw [H1P.sub_toFun]; rfl

theorem dirichletP_sub_cd {Ω : Set (CapSpace m)} (u v : H1P Ω) :
    dirichletP (u - v) = ∫ p in Ω, ((u.gx p - v.gx p) ^ 2 + ‖u.gz p - v.gz p‖ ^ 2) := by
  unfold dirichletP; rw [H1P.sub_gx, H1P.sub_gz]

/-! ## The classical gradient of the composite `F ∘ toEuclid` -/

theorem dxP_comp_toEuclid_cd {F : EuclideanSpace ℝ (Fin (m + 1)) → ℝ} (hF : ContDiff ℝ 1 F)
    (p : CapSpace m) :
    dxP (F ∘ toEuclid m) p = RobinCaps.Sobolev.Weak.classicalGrad F (toEuclid m p) 0 := by
  rw [dxP_apply, fderiv_comp_toEuclid_cd hF p (1, 0), toEuclid_axial_cd]
  rfl

theorem gradZP_comp_toEuclid_cd {F : EuclideanSpace ℝ (Fin (m + 1)) → ℝ} (hF : ContDiff ℝ 1 F)
    (p : CapSpace m) (i : Fin m) :
    gradZP (F ∘ toEuclid m) p i
      = RobinCaps.Sobolev.Weak.classicalGrad F (toEuclid m p) i.succ := by
  rw [gradZP_apply, fderiv_comp_toEuclid_cd hF p (0, EuclideanSpace.single i 1),
    toEuclid_transverse_cd]
  rfl

/-! ## Transport of the mass and Dirichlet error to `EuclideanSpace ℝ (Fin (m+1))` -/

/-- **The `L²` error of a `C¹` approximant transports exactly.** -/
theorem massP_sub_ofCompactSupport_cd {Ω : Set (CapSpace m)} (u : H1P Ω)
    {F : EuclideanSpace ℝ (Fin (m + 1)) → ℝ} (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) :
    massP (u - H1P.ofCompactSupport Ω (F ∘ toEuclid m) (contDiff_comp_toEuclid_cd hF)
        (hasCompactSupport_comp_toEuclid_cd hFc))
      = RobinCaps.Sobolev.Weak.mass (transportH1P_cd u
          - RobinCaps.Sobolev.Weak.H1.ofCompactSupport (toEuclid m '' Ω) F hF hFc) := by
  rw [RobinCaps.Compact.mass_sub, massP_sub_cd,
    setIntegral_toEuclid_image_cd Ω
      (fun x => ((transportH1P_cd u).toFun x
        - (RobinCaps.Sobolev.Weak.H1.ofCompactSupport (toEuclid m '' Ω) F hF hFc).toFun x) ^ 2)]
  have hfeq : (fun p => ((transportH1P_cd u).toFun (toEuclid m p)
        - (RobinCaps.Sobolev.Weak.H1.ofCompactSupport (toEuclid m '' Ω) F hF hFc).toFun
            (toEuclid m p)) ^ 2)
      = fun p => (u.toFun p
        - (H1P.ofCompactSupport Ω (F ∘ toEuclid m) (contDiff_comp_toEuclid_cd hF)
            (hasCompactSupport_comp_toEuclid_cd hFc)).toFun p) ^ 2 := by
    funext p
    simp only [transportH1P_cd, Function.comp_apply, ofEuclid_toEuclid,
      RobinCaps.Sobolev.Weak.H1.ofCompactSupport_toFun, H1P.ofCompactSupport_toFun]
  rw [hfeq]

theorem toEuclid_sub_cd (p q : CapSpace m) : toEuclid m (p - q) = toEuclid m p - toEuclid m q := by
  rw [sub_eq_add_neg, sub_eq_add_neg, toEuclid_add_cd, ← neg_one_smul ℝ q, toEuclid_smul_cd,
    neg_one_smul]

theorem classicalGrad_comp_toEuclid_eq_cd {F : EuclideanSpace ℝ (Fin (m + 1)) → ℝ}
    (hF : ContDiff ℝ 1 F) (p : CapSpace m) :
    RobinCaps.Sobolev.Weak.classicalGrad F (toEuclid m p)
      = toEuclid m (dxP (F ∘ toEuclid m) p, gradZP (F ∘ toEuclid m) p) := by
  refine PiLp.ext fun j => ?_
  refine Fin.cases ?_ ?_ j
  · rw [toEuclid_apply_zero, dxP_comp_toEuclid_cd hF]
  · intro i
    rw [toEuclid_apply_succ, gradZP_comp_toEuclid_cd hF]

/-- **The Dirichlet error of a `C¹` approximant transports exactly.** -/
theorem dirichletP_sub_ofCompactSupport_cd {Ω : Set (CapSpace m)} (u : H1P Ω)
    {F : EuclideanSpace ℝ (Fin (m + 1)) → ℝ} (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) :
    dirichletP (u - H1P.ofCompactSupport Ω (F ∘ toEuclid m) (contDiff_comp_toEuclid_cd hF)
        (hasCompactSupport_comp_toEuclid_cd hFc))
      = RobinCaps.Sobolev.Weak.dirichlet (transportH1P_cd u
          - RobinCaps.Sobolev.Weak.H1.ofCompactSupport (toEuclid m '' Ω) F hF hFc) := by
  rw [RobinCaps.Compact.dirichlet_sub, dirichletP_sub_cd,
    setIntegral_toEuclid_image_cd Ω
      (fun x => ‖(transportH1P_cd u).grad x
        - (RobinCaps.Sobolev.Weak.H1.ofCompactSupport (toEuclid m '' Ω) F hF hFc).grad x‖ ^ 2)]
  have hfeq : (fun p => ‖(transportH1P_cd u).grad (toEuclid m p)
        - (RobinCaps.Sobolev.Weak.H1.ofCompactSupport (toEuclid m '' Ω) F hF hFc).grad
            (toEuclid m p)‖ ^ 2)
      = fun p => ((u.gx p
          - (H1P.ofCompactSupport Ω (F ∘ toEuclid m) (contDiff_comp_toEuclid_cd hF)
              (hasCompactSupport_comp_toEuclid_cd hFc)).gx p) ^ 2
        + ‖u.gz p
          - (H1P.ofCompactSupport Ω (F ∘ toEuclid m) (contDiff_comp_toEuclid_cd hF)
              (hasCompactSupport_comp_toEuclid_cd hFc)).gz p‖ ^ 2) := by
    funext p
    show ‖gTildeCd u.gx u.gz (toEuclid m p)
        - RobinCaps.Sobolev.Weak.classicalGrad F (toEuclid m p)‖ ^ 2 = _
    have hgT : gTildeCd u.gx u.gz (toEuclid m p) = toEuclid m (u.gx p, u.gz p) := by
      simp [gTildeCd, ofEuclid_toEuclid]
    rw [hgT, classicalGrad_comp_toEuclid_eq_cd hF, ← toEuclid_sub_cd, norm_toEuclid_sq,
      H1P.ofCompactSupport_gx, H1P.ofCompactSupport_gz]
    rfl
  rw [hfeq]

/-! ## Generic dilation and mollification on a bounded convex open set

The remainder of this file redoes, for a *general* bounded convex open `Ω ⊆ EuclideanSpace ℝ
(Fin n)` with `0 ∈ Ω`, the two approximation steps of `RobinCaps/Compact/Approx.lean` (which are
specific to `Ω = ball 0 R`).  The key simplifications relative to the ball case:

* `Ω` is *star-shaped* about `0` (`star_shaped_cd`), so `x ↦ u (lam • x)` is already defined on
  `Ω` itself for `0 ≤ lam ≤ 1`, and its closeness to `u` in `L²` follows from the *global*
  convergence facts of `RobinCaps/Compact/L2Approx.lean` (`exists_lam_dilate_close`,
  `exists_delta_conv_close`), which hold on all of `E` and do not mention balls at all.
* The only genuinely new geometric fact needed is a uniform *gap*: for `lam < 1`, the compact
  set `closure Ω` has positive distance to the complement of the open dilated domain
  `Ω_lam = (lam • ·) ⁻¹' Ω ⊇ closure Ω` (`smul_closure_subset_cd`), which replaces the ball
  arithmetic `‖x‖ + δ < R` of `RobinCaps/Compact/WeakGradMollify.lean` by the generic fact
  `Metric.ball_infDist_compl_subset`. -/

section DilateMollify

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

open RobinCaps.Sobolev.Weak RobinCaps.Compact

/-! ### Zero-extension on a general open set -/

/-- The zero-extension of `u : Weak.H1 Ω` to all of `E`, for a general open set `Ω`. -/
def extCd {Ω : Set E} (u : RobinCaps.Sobolev.Weak.H1 Ω) : E → ℝ := Ω.indicator u.toFun

/-- The zero-extension of the `i`-th component of the weak gradient. -/
def extGradCd {Ω : Set E} (u : RobinCaps.Sobolev.Weak.H1 Ω) (i : Fin n) : E → ℝ :=
  Ω.indicator fun y => u.grad y i

theorem extCd_apply_of_mem {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (u : RobinCaps.Sobolev.Weak.H1 Ω) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Ω) :
    extCd u x = u.toFun x := by unfold extCd; exact indicator_of_mem hx _

theorem extCd_apply_of_not_mem {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (u : RobinCaps.Sobolev.Weak.H1 Ω) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∉ Ω) :
    extCd u x = 0 := by unfold extCd; exact indicator_of_notMem hx _

theorem extGradCd_apply_of_mem {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (u : RobinCaps.Sobolev.Weak.H1 Ω) (i : Fin n) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Ω) :
    extGradCd u i x = u.grad x i := by unfold extGradCd; exact indicator_of_mem hx _

theorem extGradCd_apply_of_not_mem {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (u : RobinCaps.Sobolev.Weak.H1 Ω) (i : Fin n) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∉ Ω) :
    extGradCd u i x = 0 := by unfold extGradCd; exact indicator_of_notMem hx _

theorem memLp_extCd {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (u : RobinCaps.Sobolev.Weak.H1 Ω) (hΩ : MeasurableSet Ω) :
    MemLp (extCd u) 2 volume := by
  unfold extCd
  rw [memLp_indicator_iff_restrict hΩ]
  exact u.memL2

theorem memLp_extGradCd {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (u : RobinCaps.Sobolev.Weak.H1 Ω) (hΩ : MeasurableSet Ω) (i : Fin n) :
    MemLp (extGradCd u i) 2 volume := by
  unfold extGradCd
  rw [memLp_indicator_iff_restrict hΩ]
  exact RobinCaps.Sobolev.Weak.memLp_two_comp u.grad_memL2 i

theorem hasCompactSupport_extCd {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (u : RobinCaps.Sobolev.Weak.H1 Ω) {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hsub : Ω ⊆ K) : HasCompactSupport (extCd u) :=
  HasCompactSupport.intro hK fun _ hx => extCd_apply_of_not_mem u fun h => hx (hsub h)

theorem hasCompactSupport_extGradCd {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (u : RobinCaps.Sobolev.Weak.H1 Ω) (i : Fin n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (hsub : Ω ⊆ K) : HasCompactSupport (extGradCd u i) :=
  HasCompactSupport.intro hK fun _ hx => extGradCd_apply_of_not_mem u i fun h => hx (hsub h)

/-! ### The dilated domain and the uniform gap -/

theorem star_shaped_cd {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (hconv : Convex ℝ Ω)
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ Ω) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Ω)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) : lam • x ∈ Ω := by
  have h := hconv h0 hx (by linarith : (0 : ℝ) ≤ 1 - lam) hlam0 (by ring)
  simpa using h

/-- The dilated domain `(fun x => lam • x) ⁻¹' Ω`. -/
def dilatedDomainCd {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (lam : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) := (fun x => lam • x) ⁻¹' Ω

theorem self_subset_dilatedDomain_cd {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hconv : Convex ℝ Ω) (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ Ω) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlam1 : lam ≤ 1) : Ω ⊆ dilatedDomainCd Ω lam :=
  fun _ hx => star_shaped_cd hconv h0 hx hlam0 hlam1

theorem isOpen_dilatedDomain_cd {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (hopen : IsOpen Ω)
    (lam : ℝ) : IsOpen (dilatedDomainCd Ω lam) :=
  hopen.preimage (continuous_const_smul lam)

theorem closure_subset_dilatedDomain_cd {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hconv : Convex ℝ Ω) (hopen : IsOpen Ω) (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ Ω) {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) : closure Ω ⊆ dilatedDomainCd Ω lam := by
  intro y hy
  show lam • y ∈ Ω
  have hint : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior Ω := by rwa [hopen.interior_eq]
  have hkey := hconv.combo_interior_closure_mem_interior hint hy (a := 1 - lam) (b := lam)
    (by linarith) hlam0 (by ring)
  rw [hopen.interior_eq] at hkey
  simpa using hkey

/-- **The uniform mollification gap.**  For `Ω` bounded, convex, open, `0 ∈ Ω` and `lam < 1`,
there is `r > 0` such that every `x ∈ closure Ω` has `closedBall x r ⊆ Ω_lam`, replacing the
ball-specific fact `‖x‖ + δ < R ⟹ closedBall x δ ⊆ ball 0 R`. -/
theorem exists_gap_cd {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (hconv : Convex ℝ Ω)
    (hopen : IsOpen Ω) (hbdd : Bornology.IsBounded Ω) (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ Ω)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ closure Ω, Metric.closedBall x r ⊆ dilatedDomainCd Ω lam := by
  have hK : IsCompact (closure Ω) := hbdd.isCompact_closure
  have hsub : closure Ω ⊆ dilatedDomainCd Ω lam :=
    closure_subset_dilatedDomain_cd hconv hopen h0 hlam0.le hlam1
  obtain ⟨δ, hδpos, hδsub⟩ :=
    hK.exists_thickening_subset_open (isOpen_dilatedDomain_cd hopen lam) hsub
  refine ⟨δ / 2, by linarith, fun x hx y hy => ?_⟩
  refine hδsub (Metric.mem_thickening_iff.mpr ⟨x, hx, ?_⟩)
  rw [Metric.mem_closedBall] at hy
  calc dist y x ≤ δ / 2 := hy
    _ < δ := by linarith

/-! ### Restriction, and the dilation as an element of `Weak.H1 Ω` itself -/

/-- Restricting an `H¹` element from `D` to a subset `D' ⊆ D`. -/
def restrictH1Cd {n : ℕ} {D D' : Set (EuclideanSpace ℝ (Fin n))} (hsub : D' ⊆ D)
    (u : RobinCaps.Sobolev.Weak.H1 D) : RobinCaps.Sobolev.Weak.H1 D' where
  toFun := u.toFun
  grad := u.grad
  memL2 := u.memL2.mono_measure (Measure.restrict_mono hsub le_rfl)
  grad_memL2 := u.grad_memL2.mono_measure (Measure.restrict_mono hsub le_rfl)
  hasWeakGrad := u.hasWeakGrad.mono hsub

@[simp] theorem restrictH1Cd_toFun {n : ℕ} {D D' : Set (EuclideanSpace ℝ (Fin n))}
    (hsub : D' ⊆ D) (u : RobinCaps.Sobolev.Weak.H1 D) :
    (restrictH1Cd hsub u).toFun = u.toFun := rfl

@[simp] theorem restrictH1Cd_grad {n : ℕ} {D D' : Set (EuclideanSpace ℝ (Fin n))}
    (hsub : D' ⊆ D) (u : RobinCaps.Sobolev.Weak.H1 D) :
    (restrictH1Cd hsub u).grad = u.grad := rfl

/-- **Dilation on the wider domain `Ω_lam`.**  This is the exact analogue of `dilate` in
`RobinCaps/Compact/Dilation.lean`, except that `Ω_lam` need not be a ball. -/
def dilateWideCd {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩmeas : MeasurableSet Ω)
    (u : RobinCaps.Sobolev.Weak.H1 Ω) {lam : ℝ} (hlam0 : 0 < lam) :
    RobinCaps.Sobolev.Weak.H1 (dilatedDomainCd Ω lam) where
  toFun := fun x => u.toFun (lam • x)
  grad := fun x => lam • u.grad (lam • x)
  memL2 := memLp_comp_smul_restrict hlam0 hΩmeas u.memL2
  grad_memL2 := (memLp_comp_smul_restrict hlam0 hΩmeas u.grad_memL2).const_smul lam
  hasWeakGrad := hasWeakGrad_comp_smul hlam0 hΩmeas u.hasWeakGrad

@[simp] theorem dilateWideCd_toFun {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩmeas : MeasurableSet Ω) (u : RobinCaps.Sobolev.Weak.H1 Ω) {lam : ℝ} (hlam0 : 0 < lam) :
    (dilateWideCd hΩmeas u hlam0).toFun = fun x => u.toFun (lam • x) := rfl

@[simp] theorem dilateWideCd_grad {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩmeas : MeasurableSet Ω) (u : RobinCaps.Sobolev.Weak.H1 Ω) {lam : ℝ} (hlam0 : 0 < lam) :
    (dilateWideCd hΩmeas u hlam0).grad = fun x => lam • u.grad (lam • x) := rfl

/-- **Dilation, restricted back to `Ω`** using star-shapedness. -/
def dilateCd {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (hconv : Convex ℝ Ω)
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ Ω) (hΩmeas : MeasurableSet Ω)
    (u : RobinCaps.Sobolev.Weak.H1 Ω) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    RobinCaps.Sobolev.Weak.H1 Ω :=
  restrictH1Cd (self_subset_dilatedDomain_cd hconv h0 hlam0.le hlam1.le)
    (dilateWideCd hΩmeas u hlam0)

@[simp] theorem dilateCd_toFun {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (hconv : Convex ℝ Ω)
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ Ω) (hΩmeas : MeasurableSet Ω)
    (u : RobinCaps.Sobolev.Weak.H1 Ω) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    (dilateCd hconv h0 hΩmeas u hlam0 hlam1).toFun = fun x => u.toFun (lam • x) := rfl

@[simp] theorem dilateCd_grad {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (hconv : Convex ℝ Ω)
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ Ω) (hΩmeas : MeasurableSet Ω)
    (u : RobinCaps.Sobolev.Weak.H1 Ω) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    (dilateCd hconv h0 hΩmeas u hlam0 hlam1).grad = fun x => lam • u.grad (lam • x) := rfl

/-! ### Mass and Dirichlet errors of the dilation, via the global zero-extension -/

theorem toFun_dilate_eq_extCd_cd {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (hconv : Convex ℝ Ω)
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ Ω) (u : RobinCaps.Sobolev.Weak.H1 Ω) {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Ω) :
    u.toFun (lam • x) = extCd u (lam • x) :=
  (extCd_apply_of_mem u (star_shaped_cd hconv h0 hx hlam0 hlam1)).symm

theorem dilate_mass_le_cd {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (hconv : Convex ℝ Ω)
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ Ω) (hΩmeas : MeasurableSet Ω)
    (u : RobinCaps.Sobolev.Weak.H1 Ω) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    (∫ x in Ω, (u.toFun (lam • x) - u.toFun x) ^ 2)
      ≤ ∫ x : EuclideanSpace ℝ (Fin n), (extCd u (lam • x) - extCd u x) ^ 2 := by
  have hint : Integrable (fun x => (extCd u (lam • x) - extCd u x) ^ 2)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    ((memLp_comp_smul (memLp_extCd u hΩmeas) hlam0).sub (memLp_extCd u hΩmeas)).integrable_sq
  have heq : Set.EqOn (fun x => (u.toFun (lam • x) - u.toFun x) ^ 2)
      (fun x => (extCd u (lam • x) - extCd u x) ^ 2) Ω := by
    intro x hx
    simp only
    rw [toFun_dilate_eq_extCd_cd hconv h0 u hlam0.le hlam1 hx, extCd_apply_of_mem u hx]
  calc (∫ x in Ω, (u.toFun (lam • x) - u.toFun x) ^ 2)
      = ∫ x in Ω, (extCd u (lam • x) - extCd u x) ^ 2 := setIntegral_congr_fun hΩmeas heq
    _ ≤ ∫ x : EuclideanSpace ℝ (Fin n), (extCd u (lam • x) - extCd u x) ^ 2 :=
        setIntegral_le_integral hint (Eventually.of_forall fun _ => sq_nonneg _)

theorem dilate_grad_component_le_cd {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hconv : Convex ℝ Ω) (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ Ω) (hΩmeas : MeasurableSet Ω)
    (u : RobinCaps.Sobolev.Weak.H1 Ω) (i : Fin n) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    (∫ x in Ω, (lam * u.grad (lam • x) i - u.grad x i) ^ 2)
      ≤ 2 * lam ^ 2 * (∫ x : EuclideanSpace ℝ (Fin n),
          (extGradCd u i (lam • x) - extGradCd u i x) ^ 2)
        + 2 * (lam - 1) ^ 2 * ∫ x : EuclideanSpace ℝ (Fin n), extGradCd u i x ^ 2 := by
  set G : EuclideanSpace ℝ (Fin n) → ℝ := extGradCd u i with hGdef
  have hGmem : MemLp G 2 volume := memLp_extGradCd u hΩmeas i
  have hGlam : MemLp (fun x => G (lam • x)) 2 volume := memLp_comp_smul hGmem hlam0
  have heq : Set.EqOn (fun x => (lam * u.grad (lam • x) i - u.grad x i) ^ 2)
      (fun x => (lam * (G (lam • x) - G x) + (lam - 1) * G x) ^ 2) Ω := by
    intro x hx
    have h1 : u.grad (lam • x) i = G (lam • x) :=
      (extGradCd_apply_of_mem u i (star_shaped_cd hconv h0 hx hlam0.le hlam1)).symm
    have h2 : u.grad x i = G x := (extGradCd_apply_of_mem u i hx).symm
    simp only [hGdef] at h1 h2 ⊢
    rw [h1, h2]; ring_nf
  have hpt : ∀ x, (lam * (G (lam • x) - G x) + (lam - 1) * G x) ^ 2
      ≤ 2 * lam ^ 2 * (G (lam • x) - G x) ^ 2 + 2 * (lam - 1) ^ 2 * G x ^ 2 := by
    intro x
    nlinarith [sq_nonneg (lam * (G (lam • x) - G x) - (lam - 1) * G x)]
  have hint1 : Integrable (fun x => (G (lam • x) - G x) ^ 2) volume :=
    (hGlam.sub hGmem).integrable_sq
  have hint2 : Integrable (fun x => G x ^ 2) volume := hGmem.integrable_sq
  have hint : Integrable (fun x => 2 * lam ^ 2 * (G (lam • x) - G x) ^ 2
      + 2 * (lam - 1) ^ 2 * G x ^ 2) volume :=
    (hint1.const_mul _).add (hint2.const_mul _)
  have hlin : MemLp (fun x => lam * (G (lam • x) - G x) + (lam - 1) * G x) 2 volume :=
    ((hGlam.sub hGmem).const_smul lam).add (hGmem.const_smul (lam - 1))
  have hint0 : Integrable (fun x => (lam * (G (lam • x) - G x) + (lam - 1) * G x) ^ 2) volume :=
    hlin.integrable_sq
  calc (∫ x in Ω, (lam * u.grad (lam • x) i - u.grad x i) ^ 2)
      = ∫ x in Ω, (lam * (G (lam • x) - G x) + (lam - 1) * G x) ^ 2 :=
        setIntegral_congr_fun hΩmeas heq
    _ ≤ ∫ x in Ω, (2 * lam ^ 2 * (G (lam • x) - G x) ^ 2 + 2 * (lam - 1) ^ 2 * G x ^ 2) :=
        setIntegral_mono_on hint0.integrableOn hint.integrableOn hΩmeas (fun x _ => hpt x)
    _ ≤ ∫ x : EuclideanSpace ℝ (Fin n),
          2 * lam ^ 2 * (G (lam • x) - G x) ^ 2 + 2 * (lam - 1) ^ 2 * G x ^ 2 :=
        setIntegral_le_integral hint (Eventually.of_forall fun x => by positivity)
    _ = 2 * lam ^ 2 * (∫ x : EuclideanSpace ℝ (Fin n), (G (lam • x) - G x) ^ 2)
          + 2 * (lam - 1) ^ 2 * ∫ x : EuclideanSpace ℝ (Fin n), G x ^ 2 := by
        rw [integral_add (hint1.const_mul _) (hint2.const_mul _), integral_const_mul,
          integral_const_mul]

theorem integrable_dilate_grad_component_cd {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hconv : Convex ℝ Ω) (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ Ω) (hΩmeas : MeasurableSet Ω)
    (u : RobinCaps.Sobolev.Weak.H1 Ω) (i : Fin n) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    IntegrableOn (fun x => (lam * u.grad (lam • x) i - u.grad x i) ^ 2) Ω volume := by
  set G : EuclideanSpace ℝ (Fin n) → ℝ := extGradCd u i with hGdef
  have hGmem : MemLp G 2 volume := memLp_extGradCd u hΩmeas i
  have hGlam : MemLp (fun x => G (lam • x)) 2 volume := memLp_comp_smul hGmem hlam0
  have hlin : MemLp (fun x => lam * (G (lam • x) - G x) + (lam - 1) * G x) 2 volume :=
    ((hGlam.sub hGmem).const_smul lam).add (hGmem.const_smul (lam - 1))
  have hint0 : Integrable (fun x => (lam * (G (lam • x) - G x) + (lam - 1) * G x) ^ 2) volume :=
    hlin.integrable_sq
  have heq : Set.EqOn (fun x => (lam * u.grad (lam • x) i - u.grad x i) ^ 2)
      (fun x => (lam * (G (lam • x) - G x) + (lam - 1) * G x) ^ 2) Ω := by
    intro x hx
    have h1 : u.grad (lam • x) i = G (lam • x) :=
      (extGradCd_apply_of_mem u i (star_shaped_cd hconv h0 hx hlam0.le hlam1)).symm
    have h2 : u.grad x i = G x := (extGradCd_apply_of_mem u i hx).symm
    simp only [hGdef] at h1 h2 ⊢
    rw [h1, h2]; ring_nf
  exact (hint0.integrableOn).congr_fun heq.symm hΩmeas

theorem dirichlet_dilate_eq_cd {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (hconv : Convex ℝ Ω)
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ Ω) (hΩmeas : MeasurableSet Ω)
    (u : RobinCaps.Sobolev.Weak.H1 Ω) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    RobinCaps.Sobolev.Weak.dirichlet (dilateCd hconv h0 hΩmeas u hlam0 hlam1 - u)
      = ∫ x in Ω, ∑ i : Fin n, (lam * u.grad (lam • x) i - u.grad x i) ^ 2 := by
  unfold RobinCaps.Sobolev.Weak.dirichlet
  rw [RobinCaps.Compact.H1.sub_grad]
  refine setIntegral_congr_fun hΩmeas fun x _ => ?_
  rw [Pi.sub_apply, dilateCd_grad, RobinCaps.Compact.norm_sq_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]

/-- **The Dirichlet error of the dilation.** -/
theorem dirichlet_dilate_le_cd {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (hconv : Convex ℝ Ω)
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ Ω) (hΩmeas : MeasurableSet Ω)
    (u : RobinCaps.Sobolev.Weak.H1 Ω) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    RobinCaps.Sobolev.Weak.dirichlet (dilateCd hconv h0 hΩmeas u hlam0 hlam1 - u)
      ≤ ∑ i : Fin n, (2 * lam ^ 2 * (∫ x : EuclideanSpace ℝ (Fin n),
            (extGradCd u i (lam • x) - extGradCd u i x) ^ 2)
          + 2 * (lam - 1) ^ 2 * ∫ x : EuclideanSpace ℝ (Fin n), extGradCd u i x ^ 2) := by
  rw [dirichlet_dilate_eq_cd hconv h0 hΩmeas u hlam0 hlam1]
  have hswap : (∫ x in Ω, ∑ i : Fin n, (lam * u.grad (lam • x) i - u.grad x i) ^ 2)
      = ∑ i : Fin n, ∫ x in Ω, (lam * u.grad (lam • x) i - u.grad x i) ^ 2 :=
    integral_finset_sum _ fun i _ =>
      integrable_dilate_grad_component_cd hconv h0 hΩmeas u i hlam0 hlam1.le
  rw [hswap]
  exact Finset.sum_le_sum fun i _ =>
    dilate_grad_component_le_cd hconv h0 hΩmeas u i hlam0 hlam1.le

/-! ### Existence of a good dilation parameter -/

/-- **The dilation step.**  For `η > 0` there is `0 < lam < 1` such that the dilation
`dilateCd` is `η`-close to `u` in mass and Dirichlet energy together. -/
theorem exists_dilate_close_cd {n : ℕ} (hn : 0 < n) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hconv : Convex ℝ Ω) (hopen : IsOpen Ω) (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ Ω)
    (u : RobinCaps.Sobolev.Weak.H1 Ω) {η : ℝ} (hη : 0 < η) :
    ∃ lam : ℝ, ∃ _ : 0 < lam, ∃ _ : lam < 1, ∀ hlam0 : 0 < lam, ∀ hlam1 : lam < 1,
      RobinCaps.Sobolev.Weak.mass (dilateCd hconv h0 hopen.measurableSet u hlam0 hlam1 - u)
        + RobinCaps.Sobolev.Weak.dirichlet
            (dilateCd hconv h0 hopen.measurableSet u hlam0 hlam1 - u) ≤ η := by
  have hΩmeas : MeasurableSet Ω := hopen.measurableSet
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  -- the mass threshold
  obtain ⟨lam0m, hlam0m, hlam1m, hmass⟩ :=
    exists_lam_dilate_close (memLp_extCd u hΩmeas) (η := η / 4) (by positivity)
  -- the per-component dirichlet thresholds
  choose lam0d hlam0d hlam1d hdirb using
    fun i : Fin n => exists_lam_dilate_close (memLp_extGradCd u hΩmeas i)
      (η := η / (8 * (n : ℝ))) (by positivity)
  obtain ⟨i0, hi0⟩ := Finite.exists_max lam0d
  -- the constant controlling the `(1-lam)²` term
  set Bsum : ℝ := ∑ i : Fin n, ∫ x : EuclideanSpace ℝ (Fin n), extGradCd u i x ^ 2 with hBsumdef
  have hBsum0 : 0 ≤ Bsum := Finset.sum_nonneg fun i _ => integral_nonneg fun _ => sq_nonneg _
  set t0 : ℝ := Real.sqrt (η / (8 * Bsum + 1)) with ht0def
  have ht0pos : 0 < t0 := Real.sqrt_pos.2 (by positivity)
  have ht0sq : t0 ^ 2 = η / (8 * Bsum + 1) := Real.sq_sqrt (by positivity)
  -- combine all the thresholds
  set lam0 : ℝ := max (max (1 / 2) lam0m) (max (lam0d i0) (1 - t0)) with hlam0def
  have hlam0lt1 : lam0 < 1 := by
    refine max_lt (max_lt (by norm_num) hlam1m) (max_lt (hlam1d i0) (by linarith))
  have hlam0pos : 0 < lam0 := lt_of_lt_of_le (by norm_num) (le_trans (le_max_left _ _)
    (le_max_left _ _))
  refine ⟨(lam0 + 1) / 2, by linarith, by linarith, fun hlam0 hlam1 => ?_⟩
  set lam : ℝ := (lam0 + 1) / 2 with hlamdef
  have hlamgt : lam0 < lam := by rw [hlamdef]; linarith
  have hlamle1 : lam ≤ 1 := by rw [hlamdef]; linarith
  have hlam1' : lam < 1 := by rw [hlamdef]; linarith
  have hgtm : lam0m < lam :=
    lt_of_le_of_lt (le_trans (le_max_right (1 / 2 : ℝ) lam0m) (le_max_left _ _)) hlamgt
  have hgtd : lam0d i0 < lam :=
    lt_of_le_of_lt (le_trans (le_max_left (lam0d i0) (1 - t0)) (le_max_right _ _)) hlamgt
  have hgtt : 1 - t0 < lam :=
    lt_of_le_of_lt (le_trans (le_max_right (lam0d i0) (1 - t0)) (le_max_right _ _)) hlamgt
  -- the mass bound
  have hmassb : RobinCaps.Sobolev.Weak.mass
      (dilateCd hconv h0 hΩmeas u hlam0 hlam1 - u) ≤ η / 4 := by
    rw [RobinCaps.Compact.mass_sub]
    calc (∫ x in Ω, ((dilateCd hconv h0 hΩmeas u hlam0 hlam1).toFun x - u.toFun x) ^ 2)
        = ∫ x in Ω, (u.toFun (lam • x) - u.toFun x) ^ 2 := by rw [dilateCd_toFun]
      _ ≤ ∫ x : EuclideanSpace ℝ (Fin n), (extCd u (lam • x) - extCd u x) ^ 2 :=
          dilate_mass_le_cd hconv h0 hΩmeas u hlam0 hlamle1
      _ ≤ η / 4 := hmass lam hgtm hlamle1
  -- the dirichlet bound
  have hdirb' : ∀ i : Fin n, (2 * lam ^ 2 * (∫ x : EuclideanSpace ℝ (Fin n),
        (extGradCd u i (lam • x) - extGradCd u i x) ^ 2)
      + 2 * (lam - 1) ^ 2 * ∫ x : EuclideanSpace ℝ (Fin n), extGradCd u i x ^ 2)
      ≤ 2 * (η / (8 * (n : ℝ))) + 2 * (lam - 1) ^ 2 * ∫ x : EuclideanSpace ℝ (Fin n),
          extGradCd u i x ^ 2 := by
    intro i
    have hb := hdirb i lam (lt_of_le_of_lt (hi0 i) hgtd) hlamle1
    have hA0 : (0:ℝ) ≤ ∫ x : EuclideanSpace ℝ (Fin n),
        (extGradCd u i (lam • x) - extGradCd u i x) ^ 2 := integral_nonneg fun _ => sq_nonneg _
    have hlamsq : lam ^ 2 ≤ 1 := by nlinarith
    have h1 : 2 * lam ^ 2 * (∫ x : EuclideanSpace ℝ (Fin n),
        (extGradCd u i (lam • x) - extGradCd u i x) ^ 2) ≤ 2 * (η / (8 * (n : ℝ))) := by
      nlinarith [hb, hA0, hlamsq]
    linarith
  have hsum1 : ∑ i : Fin n, (2 * (η / (8 * (n : ℝ)))
      + 2 * (lam - 1) ^ 2 * ∫ x : EuclideanSpace ℝ (Fin n), extGradCd u i x ^ 2)
      = 2 * (η / 8) + 2 * (lam - 1) ^ 2 * Bsum := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Finset.mul_sum, ← hBsumdef]
    have : (n : ℝ) * (2 * (η / (8 * (n : ℝ)))) = 2 * (η / 8) := by field_simp
    rw [nsmul_eq_mul, this]
  have hstep : (1 - lam) ^ 2 < t0 ^ 2 := by
    have h1 : |1 - lam| < t0 := by rw [abs_of_pos (by linarith)]; linarith
    calc (1 - lam) ^ 2 = |1 - lam| ^ 2 := (sq_abs _).symm
      _ < t0 ^ 2 := by nlinarith [abs_nonneg (1 - lam)]
  have hdirfin : 2 * (lam - 1) ^ 2 * Bsum ≤ η / 4 := by
    have h3 : (1 - lam) ^ 2 * Bsum ≤ t0 ^ 2 * Bsum :=
      mul_le_mul_of_nonneg_right hstep.le hBsum0
    rw [ht0sq] at h3
    have h4 : Bsum / (8 * Bsum + 1) ≤ 1 / 8 := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 8 * Bsum + 1)]
      linarith
    have h5 : η / (8 * Bsum + 1) * Bsum = η * (Bsum / (8 * Bsum + 1)) := by ring
    have h6 : η * (Bsum / (8 * Bsum + 1)) ≤ η * (1 / 8) :=
      mul_le_mul_of_nonneg_left h4 hη.le
    have h8 : (lam - 1) ^ 2 = (1 - lam) ^ 2 := by ring
    rw [h8]
    linarith [h3, h5, h6]
  have hdirichb : RobinCaps.Sobolev.Weak.dirichlet
      (dilateCd hconv h0 hΩmeas u hlam0 hlam1 - u) ≤ η / 4 + η / 4 := by
    calc RobinCaps.Sobolev.Weak.dirichlet (dilateCd hconv h0 hΩmeas u hlam0 hlam1 - u)
        ≤ ∑ i : Fin n, (2 * lam ^ 2 * (∫ x : EuclideanSpace ℝ (Fin n),
              (extGradCd u i (lam • x) - extGradCd u i x) ^ 2)
            + 2 * (lam - 1) ^ 2 * ∫ x : EuclideanSpace ℝ (Fin n), extGradCd u i x ^ 2) :=
          dirichlet_dilate_le_cd hconv h0 hΩmeas u hlam0 hlam1
      _ ≤ ∑ i : Fin n, (2 * (η / (8 * (n : ℝ)))
            + 2 * (lam - 1) ^ 2 * ∫ x : EuclideanSpace ℝ (Fin n), extGradCd u i x ^ 2) :=
          Finset.sum_le_sum fun i _ => hdirb' i
      _ = 2 * (η / 8) + 2 * (lam - 1) ^ 2 * Bsum := hsum1
      _ ≤ η / 4 + η / 4 := by linarith
  linarith

/-! ### The generalized (WG) identity: mollification commutes with the weak gradient

This generalizes `RobinCaps/Compact/WeakGradMollify.lean`'s `fderiv_conv_ext` from `D = ball 0 R`
to a general open `D`: the ball-arithmetic step `closedBall x δ ⊆ ball 0 R` (from `‖x‖+δ<R`) is
replaced by the *hypothesis* `closedBall x δ ⊆ D`, supplied at the call site by the uniform gap
`exists_gap_cd`. -/

theorem locallyIntegrable_extCd {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    (hDmeas : MeasurableSet D) (v : RobinCaps.Sobolev.Weak.H1 D) :
    LocallyIntegrable (extCd v) volume :=
  (memLp_extCd v hDmeas).locallyIntegrable (by norm_num)

/-- **(WG), generalized.**  For `x` whose `δ`-ball lies in `D`, the `i`-th partial derivative of
the mollification of the zero-extension of `v ∈ Weak.H1 D` is the mollification of the
zero-extension of the `i`-th component of the weak gradient of `v`. -/
theorem fderiv_conv_extCd_cd {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    (hDmeas : MeasurableSet D) {δ : ℝ} {ρ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hρ : RobinCaps.Compact.IsMollifier δ ρ) (v : RobinCaps.Sobolev.Weak.H1 D)
    {x : EuclideanSpace ℝ (Fin n)} (hx : Metric.closedBall x δ ⊆ D) (i : Fin n) :
    fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extCd v) x (EuclideanSpace.single i 1)
      = (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extGradCd v i) x := by
  classical
  have hcont : ContDiff ℝ 1 ρ := hρ.contDiff.of_le (by simp)
  have hlocv : LocallyIntegrable (extCd v) volume := locallyIntegrable_extCd hDmeas v
  -- Step 1: differentiate under the integral sign.
  have hfd : HasFDerivAt (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extCd v)
      ((fderiv ℝ ρ ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompL
          (EuclideanSpace ℝ (Fin n)), volume] extCd v) x) x :=
    hρ.hasCompactSupport.hasFDerivAt_convolution_left _ hcont hlocv x
  have hint : Integrable (fun t => ((ContinuousLinearMap.lsmul ℝ ℝ).precompL
      (EuclideanSpace ℝ (Fin n))) (fderiv ℝ ρ t) (extCd v (x - t))) volume := by
    have h := (hρ.hasCompactSupport.fderiv ℝ).convolutionExists_left
      ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (EuclideanSpace ℝ (Fin n)))
      (hρ.contDiff.continuous_fderiv (by simp)) hlocv x
    simpa [ConvolutionExistsAt] using h
  have h2 : (fderiv ℝ ρ ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompL
        (EuclideanSpace ℝ (Fin n)), volume] extCd v) x (EuclideanSpace.single i 1)
      = ∫ t, fderiv ℝ ρ t (EuclideanSpace.single i 1) * extCd v (x - t) := by
    rw [convolution_def, ContinuousLinearMap.integral_apply hint]
    simp
  -- Step 2: substitute `y = x - t`.
  have h3 : (∫ t, fderiv ℝ ρ t (EuclideanSpace.single i 1) * extCd v (x - t))
      = ∫ y, fderiv ℝ ρ (x - y) (EuclideanSpace.single i 1) * extCd v y := by
    have h := integral_sub_left_eq_self
      (fun y => fderiv ℝ ρ (x - y) (EuclideanSpace.single i 1) * extCd v y) volume x
    simpa only [sub_sub_self] using h
  -- Step 3: restrict to `D`.
  have h4 : (∫ y, fderiv ℝ ρ (x - y) (EuclideanSpace.single i 1) * extCd v y)
      = ∫ y in D, v.toFun y * fderiv ℝ ρ (x - y) (EuclideanSpace.single i 1) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := D) (f := fun y => fderiv ℝ ρ (x - y) (EuclideanSpace.single i 1) * extCd v y)
      (fun y hy => by simp [extCd_apply_of_not_mem v hy])]
    refine setIntegral_congr_fun hDmeas fun y hy => ?_
    rw [extCd_apply_of_mem v hy]
    ring
  -- Step 4: the test function `φ y = ρ (x - y)`.
  have hsupp : ∀ y : EuclideanSpace ℝ (Fin n), ρ (x - y) ≠ 0 → y ∈ Metric.closedBall x δ := by
    intro y hy
    by_contra hmem
    refine hy (hρ.eq_zero_of_lt_norm ?_)
    have : δ < dist y x := by simpa [Metric.mem_closedBall] using hmem
    rwa [dist_eq_norm, ← norm_neg, neg_sub] at this
  have htsupp : tsupport (fun y : EuclideanSpace ℝ (Fin n) => ρ (x - y)) ⊆ Metric.closedBall x δ :=
    closure_minimal (fun y hy => hsupp y hy) isClosed_closedBall
  have hφsmooth : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin n) => ρ (x - y)) :=
    hρ.contDiff.comp (contDiff_const.sub contDiff_id)
  have hφcompact : HasCompactSupport (fun y : EuclideanSpace ℝ (Fin n) => ρ (x - y)) :=
    HasCompactSupport.intro (isCompact_closedBall x δ) fun y hy => by
      by_contra h
      exact hy (hsupp y h)
  have hφderiv : ∀ y : EuclideanSpace ℝ (Fin n),
      fderiv ℝ (fun z : EuclideanSpace ℝ (Fin n) => ρ (x - z)) y (EuclideanSpace.single i 1)
      = -fderiv ℝ ρ (x - y) (EuclideanSpace.single i 1) := by
    intro y
    have h1 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => x - z)
        (-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) y := by
      simpa using (hasFDerivAt_id y).const_sub x
    have h2' : HasFDerivAt ρ (fderiv ℝ ρ (x - y)) (x - y) :=
      (hρ.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    have h3' : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => ρ (x - z))
        ((fderiv ℝ ρ (x - y)).comp (-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))) y :=
      HasFDerivAt.comp y h2' h1
    rw [h3'.fderiv]
    simp
  -- Step 5: the weak-gradient identity for this test function.
  have hkey : (∫ y in D, v.toFun y * fderiv ℝ ρ (x - y) (EuclideanSpace.single i 1))
      = ∫ y in D, v.grad y i * ρ (x - y) := by
    have hw := v.hasWeakGrad (fun y : EuclideanSpace ℝ (Fin n) => ρ (x - y)) hφsmooth hφcompact
      (htsupp.trans hx) i
    simp only [hφderiv, mul_neg, integral_neg, neg_inj] at hw
    exact hw
  -- Step 6: recognise the right-hand side as a convolution.
  have h5 : (∫ y in D, v.grad y i * ρ (x - y))
      = (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extGradCd v i) x := by
    have h5a : (∫ y in D, v.grad y i * ρ (x - y)) = ∫ y, extGradCd v i y * ρ (x - y) := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := D) (f := fun y => extGradCd v i y * ρ (x - y))
        (fun y hy => by simp [extGradCd_apply_of_not_mem v i hy])]
      refine setIntegral_congr_fun hDmeas fun y hy => ?_
      rw [extGradCd_apply_of_mem v i hy]
    have h5b := integral_sub_left_eq_self
      (fun y => extGradCd v i y * ρ (x - y)) volume x
    simp only [sub_sub_self] at h5b
    rw [h5a, RobinCaps.Compact.IsMollifier.conv_apply, ← h5b]
    exact integral_congr_ae (Eventually.of_forall fun t => mul_comm _ _)
  rw [hfd.fderiv, h2, h3, h4, hkey, h5]

/-! ### Boundedness of the dilated domain, and compact support of the extensions -/

theorem isBounded_dilatedDomain_cd {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩbdd : Bornology.IsBounded Ω) {lam : ℝ} (hlam0 : lam ≠ 0) :
    Bornology.IsBounded (dilatedDomainCd Ω lam) := by
  obtain ⟨r, hr⟩ := hΩbdd.subset_closedBall (0 : EuclideanSpace ℝ (Fin n))
  refine Bornology.IsBounded.subset
    (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin n))) (r := r / |lam|)) ?_
  intro x hx
  have h1 : lam • x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r := hr hx
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs] at h1
  rw [Metric.mem_closedBall, dist_zero_right, le_div_iff₀ (abs_pos.mpr hlam0)]
  linarith [mul_comm |lam| ‖x‖]

theorem hasCompactSupport_extCd_of_bounded {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    (hDbdd : Bornology.IsBounded D) (v : RobinCaps.Sobolev.Weak.H1 D) :
    HasCompactSupport (extCd v) := by
  obtain ⟨r, hr⟩ := hDbdd.subset_closedBall (0 : EuclideanSpace ℝ (Fin n))
  exact hasCompactSupport_extCd v (isCompact_closedBall 0 r) hr

theorem hasCompactSupport_extGradCd_of_bounded {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    (hDbdd : Bornology.IsBounded D) (v : RobinCaps.Sobolev.Weak.H1 D) (i : Fin n) :
    HasCompactSupport (extGradCd v i) := by
  obtain ⟨r, hr⟩ := hDbdd.subset_closedBall (0 : EuclideanSpace ℝ (Fin n))
  exact hasCompactSupport_extGradCd v i (isCompact_closedBall 0 r) hr

/-! ### Mass and Dirichlet errors of the mollification -/

theorem mollify_mass_le_cd {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))} (hDmeas : MeasurableSet D)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩmeas : MeasurableSet Ω) (hΩsub : Ω ⊆ D)
    (v : RobinCaps.Sobolev.Weak.H1 D)
    {δ : ℝ} {ρ : EuclideanSpace ℝ (Fin n) → ℝ} (hρ : RobinCaps.Compact.IsMollifier δ ρ) :
    (∫ x in Ω, ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extCd v) x - v.toFun x) ^ 2)
      ≤ ∫ x : EuclideanSpace ℝ (Fin n),
          ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extCd v) x - extCd v x) ^ 2 := by
  have hGmem : MemLp (extCd v) 2 volume := memLp_extCd v hDmeas
  have hFmem : MemLp (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extCd v) 2 volume :=
    RobinCaps.Compact.memLp_conv hρ hGmem
  have hint : Integrable (fun x =>
      ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extCd v) x - extCd v x) ^ 2) volume :=
    (hFmem.sub hGmem).integrable_sq
  have heq : Set.EqOn (fun x => ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extCd v) x
        - v.toFun x) ^ 2)
      (fun x => ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extCd v) x - extCd v x) ^ 2) Ω := by
    intro x hx
    simp only [extCd_apply_of_mem v (hΩsub hx)]
  calc (∫ x in Ω, ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extCd v) x - v.toFun x) ^ 2)
      = ∫ x in Ω, ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extCd v) x - extCd v x) ^ 2 :=
        setIntegral_congr_fun hΩmeas heq
    _ ≤ _ := setIntegral_le_integral hint (Eventually.of_forall fun _ => sq_nonneg _)

theorem mollify_grad_component_eq_cd {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    (hDmeas : MeasurableSet D) {Ω : Set (EuclideanSpace ℝ (Fin n))} {r : ℝ}
    (hgap : ∀ x ∈ Ω, Metric.closedBall x r ⊆ D) (_hΩsub : Ω ⊆ D)
    (v : RobinCaps.Sobolev.Weak.H1 D) {δ : ℝ} (hδ : δ < r) {ρ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hρ : RobinCaps.Compact.IsMollifier δ ρ) (i : Fin n) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ Ω) :
    RobinCaps.Sobolev.Weak.classicalGrad (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extCd v) x i
      = (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extGradCd v i) x := by
  have hxδ : Metric.closedBall x δ ⊆ D :=
    (Metric.closedBall_subset_closedBall hδ.le).trans (hgap x hx)
  rw [RobinCaps.Sobolev.Weak.classicalGrad_apply]
  exact fderiv_conv_extCd_cd hDmeas hρ v hxδ i

theorem mollify_dirichlet_component_le_cd {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    (hDmeas : MeasurableSet D) {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩmeas : MeasurableSet Ω)
    {r : ℝ} (hgap : ∀ x ∈ Ω, Metric.closedBall x r ⊆ D) (hΩsub : Ω ⊆ D)
    (v : RobinCaps.Sobolev.Weak.H1 D) {δ : ℝ} (hδ : δ < r)
    {ρ : EuclideanSpace ℝ (Fin n) → ℝ} (hρ : RobinCaps.Compact.IsMollifier δ ρ) (i : Fin n) :
    (∫ x in Ω, (RobinCaps.Sobolev.Weak.classicalGrad
          (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extCd v) x i - v.grad x i) ^ 2)
      ≤ ∫ x : EuclideanSpace ℝ (Fin n),
          ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extGradCd v i) x - extGradCd v i x) ^ 2 := by
  have hGmem : MemLp (extGradCd v i) 2 volume := memLp_extGradCd v hDmeas i
  have hFmem : MemLp (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extGradCd v i) 2 volume :=
    RobinCaps.Compact.memLp_conv hρ hGmem
  have hint : Integrable (fun x =>
      ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extGradCd v i) x - extGradCd v i x) ^ 2)
      volume := (hFmem.sub hGmem).integrable_sq
  have heq : Set.EqOn (fun x => (RobinCaps.Sobolev.Weak.classicalGrad
        (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extCd v) x i - v.grad x i) ^ 2)
      (fun x => ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extGradCd v i) x
        - extGradCd v i x) ^ 2) Ω := by
    intro x hx
    simp only [mollify_grad_component_eq_cd hDmeas hgap hΩsub v hδ hρ i hx,
      extGradCd_apply_of_mem v i (hΩsub hx)]
  calc (∫ x in Ω, (RobinCaps.Sobolev.Weak.classicalGrad
          (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extCd v) x i - v.grad x i) ^ 2)
      = ∫ x in Ω, ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extGradCd v i) x
          - extGradCd v i x) ^ 2 := setIntegral_congr_fun hΩmeas heq
    _ ≤ _ := setIntegral_le_integral hint (Eventually.of_forall fun _ => sq_nonneg _)

theorem integrable_mollify_grad_component_cd {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    (hDmeas : MeasurableSet D) {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩmeas : MeasurableSet Ω)
    {r : ℝ} (hgap : ∀ x ∈ Ω, Metric.closedBall x r ⊆ D) (hΩsub : Ω ⊆ D)
    (v : RobinCaps.Sobolev.Weak.H1 D) {δ : ℝ} (hδ : δ < r)
    {ρ : EuclideanSpace ℝ (Fin n) → ℝ} (hρ : RobinCaps.Compact.IsMollifier δ ρ) (i : Fin n) :
    IntegrableOn (fun x => (RobinCaps.Sobolev.Weak.classicalGrad
        (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extCd v) x i - v.grad x i) ^ 2) Ω volume := by
  have hGmem : MemLp (extGradCd v i) 2 volume := memLp_extGradCd v hDmeas i
  have hFmem : MemLp (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extGradCd v i) 2 volume :=
    RobinCaps.Compact.memLp_conv hρ hGmem
  have hint0 : Integrable (fun x =>
      ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extGradCd v i) x - extGradCd v i x) ^ 2)
      volume := (hFmem.sub hGmem).integrable_sq
  have heq : Set.EqOn (fun x => (RobinCaps.Sobolev.Weak.classicalGrad
        (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extCd v) x i - v.grad x i) ^ 2)
      (fun x => ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extGradCd v i) x
        - extGradCd v i x) ^ 2) Ω := by
    intro x hx
    simp only [mollify_grad_component_eq_cd hDmeas hgap hΩsub v hδ hρ i hx,
      extGradCd_apply_of_mem v i (hΩsub hx)]
  exact hint0.integrableOn.congr_fun heq.symm hΩmeas

/-! ### Existence of a good mollification radius -/

/-- **The mollification step.**  For `η > 0` there is a globally `C^∞`, compactly supported
`F` with mass and Dirichlet errors, on `Ω`, together at most `η`. -/
theorem exists_mollify_close_cd {n : ℕ} (hn : 0 < n) {D Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hDmeas : MeasurableSet D) (hΩmeas : MeasurableSet Ω) (hΩsub : Ω ⊆ D)
    (hDbdd : Bornology.IsBounded D) {r : ℝ} (hr : 0 < r)
    (hgap : ∀ x ∈ Ω, Metric.closedBall x r ⊆ D) (v : RobinCaps.Sobolev.Weak.H1 D) {η : ℝ}
    (hη : 0 < η) :
    ∃ (F : EuclideanSpace ℝ (Fin n) → ℝ) (_ : ContDiff ℝ ∞ F) (_ : HasCompactSupport F),
      (∫ x in Ω, (F x - v.toFun x) ^ 2)
        + (∫ x in Ω, ∑ i : Fin n, (RobinCaps.Sobolev.Weak.classicalGrad F x i - v.grad x i) ^ 2)
        ≤ η := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hη2 : 0 < η / 2 := by positivity
  obtain ⟨δ0m, hδ0m, hmass⟩ :=
    RobinCaps.Compact.exists_delta_conv_close (memLp_extCd v hDmeas) (η := η / 2) hη2
  choose δ0d hδ0d hdirb using fun i : Fin n =>
    RobinCaps.Compact.exists_delta_conv_close (memLp_extGradCd v hDmeas i)
      (η := η / (2 * (n : ℝ))) (by positivity)
  obtain ⟨i0, hi0⟩ := Finite.exists_min δ0d
  set δ0 : ℝ := min r (min δ0m (δ0d i0)) with hδ0def
  have hδ0pos : 0 < δ0 := lt_min hr (lt_min hδ0m (hδ0d i0))
  set δ : ℝ := δ0 / 2 with hδdef
  have hδpos : 0 < δ := by positivity
  have hδlt : δ < δ0 := by rw [hδdef]; linarith
  have hδr : δ < r := lt_of_lt_of_le hδlt (min_le_left _ _)
  have hδm : δ < δ0m := lt_of_lt_of_le hδlt (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδd : δ < δ0d i0 := lt_of_lt_of_le hδlt (le_trans (min_le_right _ _) (min_le_right _ _))
  set ρ := RobinCaps.Compact.mollifier (n := n) δ with hρdef
  have hρmol : RobinCaps.Compact.IsMollifier δ ρ := RobinCaps.Compact.isMollifier_mollifier hδpos
  have hFc : HasCompactSupport (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extCd v) :=
    HasCompactSupport.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hρmol.hasCompactSupport
      (hasCompactSupport_extCd_of_bounded hDbdd v)
  refine ⟨ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extCd v,
    hρmol.contDiff_conv (locallyIntegrable_extCd hDmeas v), hFc, ?_⟩
  have hmassb : (∫ x in Ω,
      ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extCd v) x - v.toFun x) ^ 2) ≤ η / 2 :=
    le_trans (mollify_mass_le_cd hDmeas hΩmeas hΩsub v hρmol) (hmass δ hδpos hδm)
  have hdirsum : (∫ x in Ω, ∑ i : Fin n, (RobinCaps.Sobolev.Weak.classicalGrad
        (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extCd v) x i - v.grad x i) ^ 2) ≤ η / 2 := by
    have hswap : (∫ x in Ω, ∑ i : Fin n, (RobinCaps.Sobolev.Weak.classicalGrad
          (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extCd v) x i - v.grad x i) ^ 2)
        = ∑ i : Fin n, ∫ x in Ω, (RobinCaps.Sobolev.Weak.classicalGrad
            (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extCd v) x i - v.grad x i) ^ 2 :=
      integral_finset_sum _ fun i _ =>
        integrable_mollify_grad_component_cd hDmeas hΩmeas hgap hΩsub v hδr hρmol i
    rw [hswap]
    have hcomp : ∀ i : Fin n, (∫ x in Ω, (RobinCaps.Sobolev.Weak.classicalGrad
          (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extCd v) x i - v.grad x i) ^ 2)
        ≤ η / (2 * (n : ℝ)) := by
      intro i
      refine le_trans (mollify_dirichlet_component_le_cd hDmeas hΩmeas hgap hΩsub v hδr hρmol i) ?_
      exact hdirb i δ hδpos (lt_of_lt_of_le hδd (hi0 i))
    calc ∑ i : Fin n, (∫ x in Ω, (RobinCaps.Sobolev.Weak.classicalGrad
            (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] extCd v) x i - v.grad x i) ^ 2)
        ≤ ∑ _i : Fin n, η / (2 * (n : ℝ)) := Finset.sum_le_sum fun i _ => hcomp i
      _ = η / 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  linarith

/-! ### A crude triangle inequality, and the combined existence theorem -/

theorem mass_le_two_add_two_cd {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    (w v u : RobinCaps.Sobolev.Weak.H1 D) :
    RobinCaps.Sobolev.Weak.mass (w - u)
      ≤ 2 * RobinCaps.Sobolev.Weak.mass (w - v) + 2 * RobinCaps.Sobolev.Weak.mass (v - u) := by
  rw [RobinCaps.Compact.mass_sub, RobinCaps.Compact.mass_sub, RobinCaps.Compact.mass_sub]
  have hi1 : Integrable (fun x => (w.toFun x - v.toFun x) ^ 2) (volume.restrict D) :=
    (w.memL2.sub v.memL2).integrable_sq
  have hi2 : Integrable (fun x => (v.toFun x - u.toFun x) ^ 2) (volume.restrict D) :=
    (v.memL2.sub u.memL2).integrable_sq
  have hi0 : Integrable (fun x => (w.toFun x - u.toFun x) ^ 2) (volume.restrict D) :=
    (w.memL2.sub u.memL2).integrable_sq
  have hi3 : Integrable (fun x => 2 * (w.toFun x - v.toFun x) ^ 2
      + 2 * (v.toFun x - u.toFun x) ^ 2) (volume.restrict D) :=
    (hi1.const_mul _).add (hi2.const_mul _)
  calc (∫ x in D, (w.toFun x - u.toFun x) ^ 2)
      ≤ ∫ x in D, (2 * (w.toFun x - v.toFun x) ^ 2 + 2 * (v.toFun x - u.toFun x) ^ 2) :=
        integral_mono_ae hi0 hi3 (Eventually.of_forall fun x => by
          nlinarith [sq_nonneg ((w.toFun x - v.toFun x) - (v.toFun x - u.toFun x))])
    _ = 2 * (∫ x in D, (w.toFun x - v.toFun x) ^ 2) + 2 * ∫ x in D, (v.toFun x - u.toFun x) ^ 2 := by
        rw [integral_add (hi1.const_mul _) (hi2.const_mul _), integral_const_mul,
          integral_const_mul]

theorem norm_add_sq_le_two_cd {F : Type*} [NormedAddCommGroup F] (a b : F) :
    ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h1 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  have h0 : 0 ≤ ‖a + b‖ := norm_nonneg _
  have h2 : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := by nlinarith
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

theorem dirichlet_le_two_add_two_cd {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    (w v u : RobinCaps.Sobolev.Weak.H1 D) :
    RobinCaps.Sobolev.Weak.dirichlet (w - u) ≤
      2 * RobinCaps.Sobolev.Weak.dirichlet (w - v) + 2 * RobinCaps.Sobolev.Weak.dirichlet (v - u) := by
  rw [RobinCaps.Compact.dirichlet_sub, RobinCaps.Compact.dirichlet_sub,
    RobinCaps.Compact.dirichlet_sub]
  have hi1 : Integrable (fun x => ‖w.grad x - v.grad x‖ ^ 2) (volume.restrict D) :=
    (memLp_two_iff_integrable_sq_norm
      (w.grad_memL2.sub v.grad_memL2).aestronglyMeasurable).1 (w.grad_memL2.sub v.grad_memL2)
  have hi2 : Integrable (fun x => ‖v.grad x - u.grad x‖ ^ 2) (volume.restrict D) :=
    (memLp_two_iff_integrable_sq_norm
      (v.grad_memL2.sub u.grad_memL2).aestronglyMeasurable).1 (v.grad_memL2.sub u.grad_memL2)
  have hi0 : Integrable (fun x => ‖w.grad x - u.grad x‖ ^ 2) (volume.restrict D) :=
    (memLp_two_iff_integrable_sq_norm
      (w.grad_memL2.sub u.grad_memL2).aestronglyMeasurable).1 (w.grad_memL2.sub u.grad_memL2)
  have hi3 : Integrable (fun x => 2 * ‖w.grad x - v.grad x‖ ^ 2
      + 2 * ‖v.grad x - u.grad x‖ ^ 2) (volume.restrict D) :=
    (hi1.const_mul _).add (hi2.const_mul _)
  calc (∫ x in D, ‖w.grad x - u.grad x‖ ^ 2)
      ≤ ∫ x in D, (2 * ‖w.grad x - v.grad x‖ ^ 2 + 2 * ‖v.grad x - u.grad x‖ ^ 2) := by
        refine integral_mono_ae hi0 hi3 (Eventually.of_forall fun x => ?_)
        simp only
        have heq : w.grad x - u.grad x = (w.grad x - v.grad x) + (v.grad x - u.grad x) := by abel
        rw [heq]
        exact norm_add_sq_le_two_cd _ _
    _ = 2 * (∫ x in D, ‖w.grad x - v.grad x‖ ^ 2) + 2 * ∫ x in D, ‖v.grad x - u.grad x‖ ^ 2 := by
        rw [integral_add (hi1.const_mul _) (hi2.const_mul _), integral_const_mul,
          integral_const_mul]

/-! ### The combined existence theorem, for a general bounded convex open set -/

/-- **Density of `C¹` functions in `H¹(Ω)`**, for a general bounded convex open
`Ω ⊆ EuclideanSpace ℝ (Fin n)` with `0 ∈ Ω`, `n > 0`. -/
theorem exists_smooth_close_cd {n : ℕ} (hn : 0 < n) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hconv : Convex ℝ Ω) (hopen : IsOpen Ω) (hbdd : Bornology.IsBounded Ω)
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ Ω) (u : RobinCaps.Sobolev.Weak.H1 Ω) {η : ℝ}
    (hη : 0 < η) :
    ∃ (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F),
      RobinCaps.Sobolev.Weak.mass
          (RobinCaps.Sobolev.Weak.H1.ofCompactSupport Ω F hF hFc - u)
        + RobinCaps.Sobolev.Weak.dirichlet
            (RobinCaps.Sobolev.Weak.H1.ofCompactSupport Ω F hF hFc - u) ≤ η := by
  have hΩmeas : MeasurableSet Ω := hopen.measurableSet
  have hη4 : 0 < η / 4 := by positivity
  obtain ⟨lam, hlam0, hlam1, hdil⟩ := exists_dilate_close_cd hn hconv hopen h0 u (η := η / 4) hη4
  have hdil' := hdil hlam0 hlam1
  set D : Set (EuclideanSpace ℝ (Fin n)) := dilatedDomainCd Ω lam with hDdef
  have hDopen : IsOpen D := isOpen_dilatedDomain_cd hopen lam
  have hDmeas : MeasurableSet D := hDopen.measurableSet
  have hDbdd : Bornology.IsBounded D := isBounded_dilatedDomain_cd hbdd hlam0.ne'
  have hΩsubD : Ω ⊆ D := self_subset_dilatedDomain_cd hconv h0 hlam0.le hlam1.le
  obtain ⟨r, hrpos, hgap⟩ := exists_gap_cd hconv hopen hbdd h0 hlam0 hlam1
  set v : RobinCaps.Sobolev.Weak.H1 D := dilateWideCd hΩmeas u hlam0 with hvdef
  obtain ⟨F, hFinf, hFc, hmol⟩ := exists_mollify_close_cd hn hDmeas hΩmeas hΩsubD hDbdd hrpos
    (fun x hx => hgap x (subset_closure hx)) v (η := η / 4) hη4
  have hF : ContDiff ℝ 1 F := hFinf.of_le (by simp)
  refine ⟨F, hF, hFc, ?_⟩
  set w : RobinCaps.Sobolev.Weak.H1 Ω :=
    RobinCaps.Sobolev.Weak.H1.ofCompactSupport Ω F hF hFc with hwdef
  set dilCd : RobinCaps.Sobolev.Weak.H1 Ω := dilateCd hconv h0 hΩmeas u hlam0 hlam1
    with hdilCddef
  have hmassEq : RobinCaps.Sobolev.Weak.mass (w - dilCd) = ∫ x in Ω, (F x - v.toFun x) ^ 2 := by
    rw [RobinCaps.Compact.mass_sub]
    refine setIntegral_congr_fun hΩmeas fun x _ => ?_
    simp only [hwdef, hdilCddef, RobinCaps.Sobolev.Weak.H1.ofCompactSupport_toFun,
      dilateCd_toFun, dilateWideCd_toFun, hvdef]
  have hdirEq : RobinCaps.Sobolev.Weak.dirichlet (w - dilCd)
      = ∫ x in Ω, ∑ i : Fin n, (RobinCaps.Sobolev.Weak.classicalGrad F x i - v.grad x i) ^ 2 := by
    unfold RobinCaps.Sobolev.Weak.dirichlet
    rw [RobinCaps.Compact.H1.sub_grad]
    refine setIntegral_congr_fun hΩmeas fun x _ => ?_
    rw [Pi.sub_apply, RobinCaps.Compact.norm_sq_eq_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [PiLp.sub_apply, hwdef, hdilCddef,
      RobinCaps.Sobolev.Weak.H1.ofCompactSupport_grad, dilateCd_grad, dilateWideCd_grad, hvdef]
  have hcomb1 : RobinCaps.Sobolev.Weak.mass (w - dilCd)
      + RobinCaps.Sobolev.Weak.dirichlet (w - dilCd) ≤ η / 4 := by
    rw [hmassEq, hdirEq]; linarith [hmol]
  have htri1 := mass_le_two_add_two_cd w dilCd u
  have htri2 := dirichlet_le_two_add_two_cd w dilCd u
  linarith [hdil', hcomb1, htri1, htri2]

end DilateMollify

theorem mass_sub_comm_cd {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    (a b : RobinCaps.Sobolev.Weak.H1 D) :
    RobinCaps.Sobolev.Weak.mass (a - b) = RobinCaps.Sobolev.Weak.mass (b - a) := by
  rw [RobinCaps.Compact.mass_sub, RobinCaps.Compact.mass_sub]
  exact integral_congr_ae (Eventually.of_forall fun x => by ring)

theorem dirichlet_sub_comm_cd {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    (a b : RobinCaps.Sobolev.Weak.H1 D) :
    RobinCaps.Sobolev.Weak.dirichlet (a - b) = RobinCaps.Sobolev.Weak.dirichlet (b - a) := by
  rw [RobinCaps.Compact.dirichlet_sub, RobinCaps.Compact.dirichlet_sub]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [← norm_neg (a.grad x - b.grad x)]
  congr 1
  abel_nf

/-! ## The main theorem -/

/-- **Density of `C¹` functions in `H¹` of the thin domain.**  Every `H¹` function on the thin
domain is an `H¹`-limit of functions that are `C¹` on all of `CapSpace m` (hence continuous up
to the boundary). -/
theorem exists_c1_h1_close_cd {m : ℕ} {Cm Cp : Cap m} {L R : ℝ} (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (u : H1P (thinDomain Cm Cp L R)) {η : ℝ} (hη : 0 < η) :
    ∃ v : H1P (thinDomain Cm Cp L R), ContDiff ℝ 1 v.toFun ∧
      massP (u - v) + dirichletP (u - v) ≤ η := by
  have hconv' : Convex ℝ (thinDomainE_cd Cm Cp L R) := convex_thinDomainE_cd hR hL
  have hopen' : IsOpen (thinDomainE_cd Cm Cp L R) := isOpen_thinDomainE_cd hR hL
  have hbdd' : Bornology.IsBounded (thinDomainE_cd Cm Cp L R) := isBounded_thinDomainE_cd hR hL
  have h0' : (0 : EuclideanSpace ℝ (Fin (m + 1))) ∈ thinDomainE_cd Cm Cp L R :=
    zero_mem_thinDomainE_cd hR hL
  set ũ : RobinCaps.Sobolev.Weak.H1 (thinDomainE_cd Cm Cp L R) := transportH1P_cd u with hũdef
  obtain ⟨F, hF, hFc, hbound⟩ :=
    exists_smooth_close_cd (Nat.succ_pos m) hconv' hopen' hbdd' h0' ũ hη
  refine ⟨H1P.ofCompactSupport (thinDomain Cm Cp L R) (F ∘ toEuclid m)
      (contDiff_comp_toEuclid_cd hF) (hasCompactSupport_comp_toEuclid_cd hFc),
    contDiff_comp_toEuclid_cd hF, ?_⟩
  rw [massP_sub_ofCompactSupport_cd u hF hFc, dirichletP_sub_ofCompactSupport_cd u hF hFc,
    mass_sub_comm_cd, dirichlet_sub_comm_cd]
  exact hbound

/-- **Corollary.**  The `C¹` approximant is continuous up to the boundary of the thin domain,
i.e. on `closure (thinDomain Cm Cp L R)`; this is what a trace argument needs. -/
theorem continuousOn_closure_of_exists_c1_h1_close_cd {m : ℕ} {Cm Cp : Cap m} {L R : ℝ}
    {v : H1P (thinDomain Cm Cp L R)} (hv : ContDiff ℝ 1 v.toFun) :
    ContinuousOn v.toFun (closure (thinDomain Cm Cp L R)) :=
  hv.continuous.continuousOn

end
end RobinCaps.Sobolev
