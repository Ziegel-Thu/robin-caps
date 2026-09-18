import Mathlib
import RobinCaps.Cap.CapGeometry
import RobinCaps.ThinDomain.Rescale
import RobinCaps.Sobolev.ConvexDensity
import RobinCaps.Sobolev.PoincareConvex
import RobinCaps.Cap.LowerWeak
import RobinCaps.Cap.Sharp

/-!
# The Poincaré–Wirtinger inequality on an arbitrary admissible cap

This file closes the `CapPoincare` interface of `RobinCaps/Cap/LowerWeak.lean`
(`capPoincare_gen_pgn`) for **every** admissible cap `C : Cap m`, not just the flat cap
(`RobinCaps/Cap/PoincareFlat.lean`) or the hemisphere (`RobinCaps/Cap/PoincareHemiGen.lean`).

## Route

`H1P C.body` is first translated (`RobinCaps.Cap.bodyShift_cg` of
`RobinCaps/Cap/CapGeometry.lean`, via `H1P.rescaleP` of `RobinCaps/ThinDomain/Rescale.lean` with
the trivial scaling `c = R = 1`, an exact translation with `massP`/`dirichletP` preserved on the
nose) so that the origin becomes an interior point of a bounded convex open set, then transported
by the linear identification `toEuclid m` (`transportH1P_cd` of
`RobinCaps/Sobolev/ConvexDensity.lean`) to `Weak.H1` of a bounded convex open subset of
`EuclideanSpace ℝ (Fin (m+1))` containing `0`, where the general convex-domain Poincaré–Wirtinger
inequality `poincare_wirtinger_convex_pcx` of `RobinCaps/Sobolev/PoincareConvex.lean` applies.
Pulling the resulting inequality back along the same chain (using the *shifted* mass identity
`mass_sub_const_transport_pgn`, so that the arbitrary constant `t` produced by the convex-domain
theorem is carried along unchanged) gives exactly `CapPoincare C CP`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace RobinCaps
namespace Cap

open RobinCaps.ThinDomain RobinCaps.Sobolev RobinCaps.Sobolev.Weak RobinCaps.Domain
open RobinCaps.Sobolev.PoincareConvex

noncomputable section

variable {m : ℕ}

/-! ## Transport of the mass, Dirichlet energy, and shifted mass to `EuclideanSpace ℝ (Fin (m+1))`

These are the generic transport identities along `toEuclid m` for an arbitrary `Ω : Set
(CapSpace m)`, obtained from `setIntegral_toEuclid_image_cd` (the change of variables) and
`norm_gTildeCd_sq_cd` (the pointwise norm identity for the transported gradient) of
`RobinCaps/Sobolev/ConvexDensity.lean`. -/

/-- **The `L²` mass transports exactly along `toEuclid`.** -/
theorem mass_transport_pgn {Ω : Set (CapSpace m)} (hΩ : MeasurableSet Ω) (u : H1P Ω) :
    mass (transportH1P_cd u) = massP u := by
  show (∫ x in toEuclid m '' Ω, (transportH1P_cd u).toFun x ^ 2) = ∫ p in Ω, u.toFun p ^ 2
  rw [setIntegral_toEuclid_image_cd Ω (fun x => (transportH1P_cd u).toFun x ^ 2)]
  refine setIntegral_congr_fun hΩ fun p _ => ?_
  show (u.toFun (ofEuclid m (toEuclid m p))) ^ 2 = u.toFun p ^ 2
  rw [ofEuclid_toEuclid]

/-- **The Dirichlet energy transports exactly along `toEuclid`.** -/
theorem dirichlet_transport_pgn {Ω : Set (CapSpace m)} (hΩ : MeasurableSet Ω) (u : H1P Ω) :
    dirichlet (transportH1P_cd u) = dirichletP u := by
  show (∫ x in toEuclid m '' Ω, ‖(transportH1P_cd u).grad x‖ ^ 2)
      = ∫ p in Ω, (u.gx p ^ 2 + ‖u.gz p‖ ^ 2)
  rw [setIntegral_toEuclid_image_cd Ω (fun x => ‖(transportH1P_cd u).grad x‖ ^ 2)]
  refine setIntegral_congr_fun hΩ fun p _ => ?_
  show ‖gTildeCd u.gx u.gz (toEuclid m p)‖ ^ 2 = u.gx p ^ 2 + ‖u.gz p‖ ^ 2
  rw [norm_gTildeCd_sq_cd, ofEuclid_toEuclid]

/-- **The `L²` distance to a constant transports exactly along `toEuclid`.** -/
theorem mass_sub_const_transport_pgn {Ω : Set (CapSpace m)} (hΩ : MeasurableSet Ω) (u : H1P Ω)
    (t : ℝ) :
    (∫ x in toEuclid m '' Ω, ((transportH1P_cd u).toFun x - t) ^ 2)
      = ∫ p in Ω, (u.toFun p - t) ^ 2 := by
  rw [setIntegral_toEuclid_image_cd Ω (fun x => ((transportH1P_cd u).toFun x - t) ^ 2)]
  refine setIntegral_congr_fun hΩ fun p _ => ?_
  show (u.toFun (ofEuclid m (toEuclid m p)) - t) ^ 2 = (u.toFun p - t) ^ 2
  rw [ofEuclid_toEuclid]

/-! ## Geometry of the Euclidean image `toEuclid m '' bodyShift_cg C`

Mimicking `isOpen_thinDomainE_cd`, `convex_thinDomainE_cd`, `isBounded_thinDomainE_cd`,
`zero_mem_thinDomainE_cd` of `RobinCaps/Sobolev/ConvexDensity.lean`, for the shifted cap body in
place of the thin domain: a continuous linear equivalence (`capSpaceCLE_cd m`) carries an open /
convex / bounded set, and the origin, correctly. -/

/-- The Euclidean image of the shifted cap body is open. -/
theorem isOpen_bodyShiftE_pgn (C : Cap m) : IsOpen (toEuclid m '' bodyShift_cg C) :=
  (capSpaceCLE_cd m).toHomeomorph.isOpen_image.2 (isOpen_bodyShift_cg C)

/-- The Euclidean image of the shifted cap body is convex. -/
theorem convex_bodyShiftE_pgn (C : Cap m) : Convex ℝ (toEuclid m '' bodyShift_cg C) :=
  (convex_bodyShift_cg C).linear_image (capSpaceLinearEquiv_cd m).toLinearMap

/-- The Euclidean image of the shifted cap body is bounded: `toEuclid m` is (Lipschitz, being) a
continuous linear equivalence, so it carries bounded sets to bounded sets. -/
theorem isBounded_bodyShiftE_pgn (C : Cap m) :
    Bornology.IsBounded (toEuclid m '' bodyShift_cg C) :=
  (capSpaceCLE_cd m).lipschitz.isBounded_image (isBounded_bodyShift_cg C)

/-- The origin lies in the Euclidean image of the shifted cap body. -/
theorem zero_mem_bodyShiftE_pgn (C : Cap m) :
    (0 : EuclideanSpace ℝ (Fin (m + 1))) ∈ toEuclid m '' bodyShift_cg C :=
  ⟨0, zero_mem_bodyShift_cg C, toEuclid_zero_cd⟩

/-! ## The headline theorem -/

/-- **The Poincaré–Wirtinger inequality on an arbitrary admissible cap.**  Closes the interface
`RobinCaps.Cap.CapPoincare` for every cap, not just the flat one and the hemisphere. -/
theorem capPoincare_gen_pgn (m : ℕ) (hm : 1 ≤ m) (C : Cap m) : ∃ CP : ℝ, CapPoincare C CP := by
  have hΩ : MeasurableSet C.body := RobinCaps.ThinDomain.measurableSet_capBody C
  have hε1 : |(1 : ℝ)| = 1 := by norm_num
  obtain ⟨CP, hCPnn, hCP⟩ :=
    RobinCaps.Sobolev.PoincareConvex.poincare_wirtinger_convex_pcx (n := m + 1)
      (by omega) (convex_bodyShiftE_pgn C) (isOpen_bodyShiftE_pgn C)
      (isBounded_bodyShiftE_pgn C) (zero_mem_bodyShiftE_pgn C)
  refine ⟨CP, hCPnn, fun u => ?_⟩
  -- Step 2: translate `u` to `u' ∈ H1P (bodyShift_cg C)` by the pure axial shift.
  set u' : H1P (bodyShift_cg C) :=
    H1P.rescaleP (-C.K / 2) (1 : ℝ) (one_pos : (0 : ℝ) < 1) hε1 hΩ u with hu'def
  -- Step 4: apply the convex-domain Poincaré inequality to the transported function.
  obtain ⟨t, ht⟩ := hCP (transportH1P_cd u')
  refine ⟨t, ?_⟩
  -- Dirichlet energy is exactly preserved by the trivial rescaling and by the transport.
  have hdiru' : dirichletP u' = dirichletP u := by
    rw [hu'def, dirichletP_rescaleP]
    simp
  have hdirv : dirichlet (transportH1P_cd u') = dirichletP u' :=
    dirichlet_transport_pgn (measurableSet_bodyShift_cg C) u'
  -- The pointwise description of `u'`.
  have hu'toFun : ∀ p : CapSpace m,
      u'.toFun p = u.toFun (RobinCaps.ThinDomain.affP (-C.K / 2) 1 1 p) := by
    intro p
    simp [hu'def]
  -- The change-of-variables identity for the shifted mass, specialised to the pure translation.
  have hchange := RobinCaps.ThinDomain.setIntegral_comp_affP (-C.K / 2) (one_pos : (0 : ℝ) < 1)
    hε1 hΩ (fun q => (u.toFun q - t) ^ 2)
  simp only [one_pow, inv_one, one_mul] at hchange
  have step2 : (∫ p in C.body, (u.toFun p - t) ^ 2)
      = ∫ p in bodyShift_cg C, (u'.toFun p - t) ^ 2 := by
    rw [← hchange]
    refine setIntegral_congr_fun (measurableSet_bodyShift_cg C) fun p _ => ?_
    rw [hu'toFun p]
  have step3 : (∫ p in bodyShift_cg C, (u'.toFun p - t) ^ 2)
      = ∫ x in toEuclid m '' bodyShift_cg C, ((transportH1P_cd u').toFun x - t) ^ 2 :=
    (mass_sub_const_transport_pgn (measurableSet_bodyShift_cg C) u' t).symm
  -- Step 5: land on `CapPoincare`.
  have hmasseq : massP (u - constP C t) = ∫ p in C.body, (u.toFun p - t) ^ 2 := by
    show (∫ p in C.body, (u - constP C t).toFun p ^ 2) = ∫ p in C.body, (u.toFun p - t) ^ 2
    refine setIntegral_congr_fun hΩ fun p _ => ?_
    rw [sub_constP_toFun]
  calc massP (u - constP C t)
      = ∫ p in C.body, (u.toFun p - t) ^ 2 := hmasseq
    _ = ∫ p in bodyShift_cg C, (u'.toFun p - t) ^ 2 := step2
    _ = ∫ x in toEuclid m '' bodyShift_cg C, ((transportH1P_cd u').toFun x - t) ^ 2 := step3
    _ ≤ CP * dirichlet (transportH1P_cd u') := ht
    _ = CP * dirichletP u' := by rw [hdirv]
    _ = CP * dirichletP u := by rw [hdiru']

/-! ## Sanity check -/

/-- Specialising `capPoincare_gen_pgn` to the hemisphere recovers `capPoincare_hemi_phg`
(`RobinCaps/Cap/PoincareHemiGen.lean`), obtained there by a different route (even reflection to
the ball). -/
theorem capPoincare_gen_hemi_pgn (m : ℕ) (hm : 1 ≤ m) :
    ∃ CP : ℝ, CapPoincare (Cap.hemisphere m) CP :=
  capPoincare_gen_pgn m hm (Cap.hemisphere m)

end
end Cap
end RobinCaps
