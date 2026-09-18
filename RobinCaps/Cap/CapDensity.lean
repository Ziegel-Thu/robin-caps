import Mathlib
import RobinCaps.Cap.CapGeometry
import RobinCaps.Sobolev.ConvexDensity

/-!
# Density of globally `C¹` functions in `H¹` of a cap body

**Main theorem**: `exists_c1_h1_close_cap_cdn` — every `u ∈ H1P C.body` (for an admissible end
cap `C : Cap m`) is the `H¹`-limit (jointly in mass and Dirichlet energy) of functions `v` that
are `C¹` on all of `CapSpace m`, hence continuous up to the boundary of the cap body
(`continuousOn_closure_of_c1_cdn`).

This is the cap-body analogue of `RobinCaps.Sobolev.exists_c1_h1_close_cd`, which is stated for
the thin domain `thinDomain Cm Cp L R`.  The template proof there transports `H1P Ω` along the
linear identification `toEuclid m : CapSpace m ≃L[ℝ] EuclideanSpace ℝ (Fin (m+1))` to
`RobinCaps.Sobolev.Weak.H1` and invokes the general density theorem `exists_smooth_close_cd` for
a bounded convex open set containing the origin.  The thin domain already contains the origin, but
the cap body `C.body ⊆ {-K < s < 0}` does not, so the same argument is first run on the **shifted**
body `bodyShift_cg C` (which does contain the origin, `RobinCaps/Cap/CapGeometry.lean`), and the
result is transported back to `C.body` along the exact translation `affP (± C.K/2) 1 1`, which
preserves `massP`/`dirichletP` exactly (`massP_rescaleP`, `dirichletP_rescaleP` of
`RobinCaps/ThinDomain/Rescale.lean` with `c = R = 1`).

## Route

* `isBounded_toEuclid_image_cdn`: a bounded subset of `CapSpace m` has bounded image under
  `toEuclid m`, generically (via the Lipschitz continuity of the continuous linear equivalence
  `capSpaceCLE_cd`), replacing the thin-domain-specific `isBounded_toEuclid_image_thinDomain`.
* `isOpen_bodyShiftE_cdn`, `convex_bodyShiftE_cdn`, `isBounded_bodyShiftE_cdn`,
  `zero_mem_bodyShiftE_cdn`: the four hypotheses of `exists_smooth_close_cd` for
  `toEuclid m '' bodyShift_cg C`, transported from the corresponding facts about `bodyShift_cg C`
  itself (`RobinCaps/Cap/CapGeometry.lean`), exactly mirroring the thin-domain argument of
  `RobinCaps/Sobolev/ConvexDensity.lean`.
* `exists_c1_h1_close_bodyShift_cdn`: the density theorem on `bodyShift_cg C`, a verbatim
  transcription of `exists_c1_h1_close_cd` with `thinDomain Cm Cp L R` replaced by
  `bodyShift_cg C`.
* `affP_comp_shift_cdn`, `affP_comp_shift_symm_cdn`, `preimage_shift_back_cdn`: the elementary
  round-trip facts for the translation `affP (± C.K/2) 1 1`.
* `exists_c1_h1_close_cap_cdn`: the main theorem, obtained by shifting `u` to `bodyShift_cg C`,
  applying `exists_c1_h1_close_bodyShift_cdn`, and shifting the resulting `C¹` approximant back.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Filter
open scoped ContDiff ENNReal Topology

namespace RobinCaps.Sobolev

open RobinCaps.Cap RobinCaps.Domain RobinCaps.ThinDomain

noncomputable section

variable {m : ℕ}

/-! ## Boundedness transports generically along `toEuclid` -/

/-- **A bounded subset of `CapSpace m` has bounded image under `toEuclid`.**  Generic replacement
for the thin-domain-specific `isBounded_toEuclid_image_thinDomain`: `toEuclid m` is (the
coercion of) a continuous linear equivalence between finite-dimensional spaces, hence Lipschitz,
hence maps bounded sets to bounded sets. -/
theorem isBounded_toEuclid_image_cdn {Ω : Set (CapSpace m)} (hΩ : Bornology.IsBounded Ω) :
    Bornology.IsBounded (toEuclid m '' Ω) := by
  have hfun : (⇑(capSpaceCLE_cd m) : CapSpace m → EuclideanSpace ℝ (Fin (m + 1))) = toEuclid m :=
    rfl
  have him := (capSpaceCLE_cd m).lipschitz.isBounded_image hΩ
  rwa [hfun] at him

/-! ## The four hypotheses of `exists_smooth_close_cd` for `toEuclid m '' bodyShift_cg C` -/

theorem isOpen_bodyShiftE_cdn (C : Cap m) : IsOpen (toEuclid m '' bodyShift_cg C) :=
  (capSpaceCLE_cd m).toHomeomorph.isOpen_image.2 (isOpen_bodyShift_cg C)

theorem convex_bodyShiftE_cdn (C : Cap m) : Convex ℝ (toEuclid m '' bodyShift_cg C) :=
  (convex_bodyShift_cg C).linear_image (capSpaceLinearEquiv_cd m).toLinearMap

theorem isBounded_bodyShiftE_cdn (C : Cap m) :
    Bornology.IsBounded (toEuclid m '' bodyShift_cg C) :=
  isBounded_toEuclid_image_cdn (isBounded_bodyShift_cg C)

theorem zero_mem_bodyShiftE_cdn (C : Cap m) :
    (0 : EuclideanSpace ℝ (Fin (m + 1))) ∈ toEuclid m '' bodyShift_cg C :=
  ⟨0, zero_mem_bodyShift_cg C, toEuclid_zero_cd⟩

/-! ## Density on the shifted body -/

/-- **Density of `C¹` functions in `H¹` of the shifted cap body.**  A verbatim transcription of
`exists_c1_h1_close_cd` with `thinDomain Cm Cp L R` replaced throughout by `bodyShift_cg C`
(which already contains the origin, unlike `C.body` itself). -/
theorem exists_c1_h1_close_bodyShift_cdn {C : Cap m} (u : H1P (bodyShift_cg C)) {η : ℝ}
    (hη : 0 < η) :
    ∃ v : H1P (bodyShift_cg C), ContDiff ℝ 1 v.toFun ∧
      massP (u - v) + dirichletP (u - v) ≤ η := by
  have hconv' : Convex ℝ (toEuclid m '' bodyShift_cg C) := convex_bodyShiftE_cdn C
  have hopen' : IsOpen (toEuclid m '' bodyShift_cg C) := isOpen_bodyShiftE_cdn C
  have hbdd' : Bornology.IsBounded (toEuclid m '' bodyShift_cg C) := isBounded_bodyShiftE_cdn C
  have h0' : (0 : EuclideanSpace ℝ (Fin (m + 1))) ∈ toEuclid m '' bodyShift_cg C :=
    zero_mem_bodyShiftE_cdn C
  set ũ : RobinCaps.Sobolev.Weak.H1 (toEuclid m '' bodyShift_cg C) := transportH1P_cd u with hũdef
  obtain ⟨F, hF, hFc, hbound⟩ :=
    exists_smooth_close_cd (Nat.succ_pos m) hconv' hopen' hbdd' h0' ũ hη
  refine ⟨H1P.ofCompactSupport (bodyShift_cg C) (F ∘ toEuclid m)
      (contDiff_comp_toEuclid_cd hF) (hasCompactSupport_comp_toEuclid_cd hFc),
    contDiff_comp_toEuclid_cd hF, ?_⟩
  rw [massP_sub_ofCompactSupport_cd u hF hFc, dirichletP_sub_ofCompactSupport_cd u hF hFc,
    mass_sub_comm_cd, dirichlet_sub_comm_cd]
  exact hbound

/-! ## The round trip of the axial translation `affP (± C.K/2) 1 1` -/

theorem affP_comp_shift_cdn (C : Cap m) (p : CapSpace m) :
    affP (-C.K / 2) 1 1 (affP (C.K / 2) 1 1 p) = p := by
  have h1 : (-C.K / 2 + 1 * 1 * (C.K / 2 + 1 * 1 * p.1) : ℝ) = p.1 := by ring
  have h2 : ((1 : ℝ) • ((1 : ℝ) • p.2) : EuclideanSpace ℝ (Fin m)) = p.2 := by simp
  exact Prod.ext h1 h2

theorem affP_comp_shift_symm_cdn (C : Cap m) (p : CapSpace m) :
    affP (C.K / 2) 1 1 (affP (-C.K / 2) 1 1 p) = p := by
  have h1 : (C.K / 2 + 1 * 1 * (-C.K / 2 + 1 * 1 * p.1) : ℝ) = p.1 := by ring
  have h2 : ((1 : ℝ) • ((1 : ℝ) • p.2) : EuclideanSpace ℝ (Fin m)) = p.2 := by simp
  exact Prod.ext h1 h2

/-- **The preimage of the shifted body under the back-translation is the cap body.** -/
theorem preimage_shift_back_cdn (C : Cap m) :
    (affP (C.K / 2) 1 1 : CapSpace m → CapSpace m) ⁻¹' bodyShift_cg C = C.body := by
  ext p
  show affP (-C.K / 2) 1 1 (affP (C.K / 2) 1 1 p) ∈ C.body ↔ p ∈ C.body
  rw [affP_comp_shift_cdn C p]

/-! ## The main theorem -/

/-- **Density of globally `C¹` functions in `H¹` of an arbitrary cap body.**  The cap-body
analogue of `RobinCaps.Sobolev.exists_c1_h1_close_cd` (which is stated for the thin domain). -/
theorem exists_c1_h1_close_cap_cdn {m : ℕ} (C : Cap m) (u : H1P C.body) {η : ℝ} (hη : 0 < η) :
    ∃ v : H1P C.body, ContDiff ℝ 1 v.toFun ∧ massP (u - v) + dirichletP (u - v) ≤ η := by
  have hε1 : |(1 : ℝ)| = 1 := by norm_num
  have hCM : MeasurableSet C.body := measurableSet_capBody C
  have hBM : MeasurableSet (bodyShift_cg C) := measurableSet_bodyShift_cg C
  -- Step 1: shift `u` forward to the origin-containing body `bodyShift_cg C`.
  set u' : H1P (bodyShift_cg C) :=
    H1P.rescaleP (-C.K / 2) 1 one_pos hε1 hCM u with hu'def
  have hu'toFun : ∀ p, u'.toFun p = u.toFun (affP (-C.K / 2) 1 1 p) := by
    intro p; rw [hu'def, H1P.rescaleP_toFun]; ring
  -- Step 2: obtain the `C¹` approximant `v'` of `u'` on `bodyShift_cg C`.
  obtain ⟨v', hv', hbound⟩ := exists_c1_h1_close_bodyShift_cdn u' hη
  -- Step 3: shift `v'` back to `C.body`.
  set v : H1P C.body :=
    (preimage_shift_back_cdn C) ▸ (H1P.rescaleP (C.K / 2) 1 one_pos hε1 hBM v') with hvdef
  have hvtoFun : ∀ p, v.toFun p = v'.toFun (affP (C.K / 2) 1 1 p) := by
    intro p
    rw [hvdef]
    rw [H1P.cast_toFun, H1P.rescaleP_toFun]
    ring
  refine ⟨v, ?_, ?_⟩
  · -- `v` is `C¹`: `v.toFun = v'.toFun ∘ affP (C.K/2) 1 1`, a composite of `C¹` maps.
    have hveq : v.toFun = v'.toFun ∘ (affP (C.K / 2) 1 1 : CapSpace m → CapSpace m) := by
      funext p; exact hvtoFun p
    rw [hveq]
    exact hv'.comp ((contDiff_affP (C.K / 2) 1 1).of_le (by norm_num))
  · -- the mass/Dirichlet bound: shift `u - v` forward and identify the result with `u' - v'`.
    have hUtoFun : (H1P.rescaleP (-C.K / 2) (1 : ℝ) one_pos hε1 hCM (u - v)).toFun
        = (u' - v').toFun := by
      funext p
      rw [H1P.rescaleP_toFun, H1P.sub_toFun, H1P.sub_toFun]
      simp only [Pi.sub_apply]
      rw [hu'toFun p, hvtoFun (affP (-C.K / 2) 1 1 p), affP_comp_shift_symm_cdn C p]
      ring
    have hUgx : (H1P.rescaleP (-C.K / 2) (1 : ℝ) one_pos hε1 hCM (u - v)).gx = (u' - v').gx := by
      funext p
      simp only [H1P.rescaleP_gx, H1P.sub_gx]
      have hu'gx : u'.gx p = u.gx (affP (-C.K / 2) 1 1 p) := by
        rw [hu'def, H1P.rescaleP_gx]; ring
      have hvgx : v.gx (affP (-C.K / 2) 1 1 p) = v'.gx (affP (C.K / 2) 1 1
          (affP (-C.K / 2) 1 1 p)) := by
        rw [hvdef, H1P.cast_gx, H1P.rescaleP_gx]; ring
      rw [hu'gx, hvgx, affP_comp_shift_symm_cdn C p]
      ring
    have hUgz : (H1P.rescaleP (-C.K / 2) (1 : ℝ) one_pos hε1 hCM (u - v)).gz = (u' - v').gz := by
      funext p
      simp only [H1P.rescaleP_gz, H1P.sub_gz]
      have hu'gz : u'.gz p = u.gz (affP (-C.K / 2) 1 1 p) := by
        rw [hu'def, H1P.rescaleP_gz]; simp
      have hvgz : v.gz (affP (-C.K / 2) 1 1 p) = v'.gz (affP (C.K / 2) 1 1
          (affP (-C.K / 2) 1 1 p)) := by
        rw [hvdef, H1P.cast_gz, H1P.rescaleP_gz]; simp
      rw [hu'gz, hvgz, affP_comp_shift_symm_cdn C p]
      simp
    have hUeq : H1P.rescaleP (-C.K / 2) (1 : ℝ) one_pos hε1 hCM (u - v) = u' - v' :=
      H1P.ext hUtoFun hUgx hUgz
    have hmassU := massP_rescaleP (-C.K / 2) (1 : ℝ) one_pos hε1 hCM (u - v)
    have hdirU := dirichletP_rescaleP (-C.K / 2) (1 : ℝ) one_pos hε1 hCM (u - v)
    simp only [one_pow, inv_one, one_mul] at hmassU hdirU
    rw [hUeq] at hmassU hdirU
    linarith [hbound, hmassU, hdirU]

/-- The `C¹` approximant is continuous up to the boundary of the cap body. -/
theorem continuousOn_closure_of_c1_cdn {m : ℕ} {C : Cap m} {v : H1P C.body}
    (hv : ContDiff ℝ 1 v.toFun) : ContinuousOn v.toFun (closure C.body) :=
  hv.continuous.continuousOn

end
end RobinCaps.Sobolev
