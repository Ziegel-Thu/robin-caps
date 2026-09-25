import RobinCaps.ThinDomain.EigenIface
import RobinCaps.Compact.ConvexRellichIface

/-!
# Rellich–Kondrachov for the product model `H1P`, transported from Euclidean space

**Main theorems.**

* `rellichP_of_rellichL2_rth`: if the Euclidean Rellich–Kondrachov statement
  `RobinCaps.Compact.RellichEmbeddingL2` holds on the Euclidean image `toEuclid m '' Ω` of a
  measurable `Ω ⊆ CapSpace m`, then the product-model statement `RellichEmbeddingP Ω`
  (`RobinCaps/ThinDomain/EigenIface.lean`) holds on `Ω` itself.
* `rellichP_thin_rth`: the specialisation to the thin domain `thinDomain Cm Cp L R`, where
  the Euclidean hypothesis is phrased on `RobinCaps.Sobolev.thinDomainE_cd Cm Cp L R`, which is
  *definitionally* `toEuclid m '' thinDomain Cm Cp L R`.

## Route

`RobinCaps/Sobolev/ConvexDensity.lean` already builds the linear identification
`toEuclid m : CapSpace m ≃ EuclideanSpace ℝ (Fin (m+1))` together with the transport
`transportH1P_cd : H1P Ω → Weak.H1 (toEuclid m '' Ω)` of the weak-`H¹` layer, and proves that
`toEuclid m` is measure preserving. Two easy consequences, proved here first, say that the
forms transport *exactly* along `transportH1P_cd` (no approximation is involved, unlike the
density theorem `exists_c1_h1_close_cd` of that file):

* `massP_eq_mass_transportH1P_rth`: `massP u = mass (transportH1P_cd u)`;
* `dirichletP_eq_dirichlet_transportH1P_rth`: `dirichletP u = dirichlet (transportH1P_cd u)`.

Given a bounded sequence `u : ℕ → H1P Ω`, transporting it to `k ↦ transportH1P_cd (u k)` and
feeding it to the Euclidean Rellich–Kondrachov hypothesis `hrel` produces a subsequence `ν` and
an `L²`-limit `v` on `toEuclid m '' Ω`. Pulling `v` back along `toEuclid m` (`v' = v ∘ toEuclid m`)
gives a function on `Ω` itself: it is `L²(Ω)` because `toEuclid m` is measure preserving
(`measurePreserving_toEuclid_restrict_cd`), and the `L²` distance of `u (ν k)` to `v'` on `Ω`
equals, by the same change of variables (`setIntegral_toEuclid_image_cd`, using
`ofEuclid m ∘ toEuclid m = id`, i.e. `ofEuclid_toEuclid`), the `L²` distance of
`transportH1P_cd (u (ν k))` to `v` on `toEuclid m '' Ω`, which tends to `0` by `hrel`.

No hypothesis beyond the ones in the theorem statements is left open; no `sorry`, `admit`,
`axiom` or `native_decide` occurs in this file.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RobinCaps.ThinDomain

open RobinCaps.Domain RobinCaps.Cap RobinCaps.Sobolev

/-! ## Exact transport of the forms along `transportH1P_cd` -/

/-- **The mass transports exactly.** No approximation: `toEuclid m` is measure preserving, so a
plain change of variables identifies `massP u` with the Euclidean mass of the transported
element. -/
theorem massP_eq_mass_transportH1P_rth {m : ℕ} {Ω : Set (CapSpace m)} (u : H1P Ω) :
    massP u = RobinCaps.Sobolev.Weak.mass (transportH1P_cd u) := by
  unfold massP RobinCaps.Sobolev.Weak.mass
  rw [setIntegral_toEuclid_image_cd Ω (fun x => (transportH1P_cd u).toFun x ^ 2)]
  have hfeq : (fun p : CapSpace m => (transportH1P_cd u).toFun (toEuclid m p) ^ 2)
      = fun p => u.toFun p ^ 2 := by
    funext p
    show (u.toFun (ofEuclid m (toEuclid m p))) ^ 2 = u.toFun p ^ 2
    rw [ofEuclid_toEuclid]
  rw [hfeq]

/-- **The Dirichlet energy transports exactly.** Same change of variables, using
`norm_gTildeCd_sq_cd` to identify the transported gradient's squared norm with
`(∂ₓu)² + ‖∇_z u‖²`. -/
theorem dirichletP_eq_dirichlet_transportH1P_rth {m : ℕ} {Ω : Set (CapSpace m)} (u : H1P Ω) :
    dirichletP u = RobinCaps.Sobolev.Weak.dirichlet (transportH1P_cd u) := by
  unfold dirichletP RobinCaps.Sobolev.Weak.dirichlet
  rw [setIntegral_toEuclid_image_cd Ω (fun x => ‖(transportH1P_cd u).grad x‖ ^ 2)]
  have hfeq : (fun p : CapSpace m => ‖(transportH1P_cd u).grad (toEuclid m p)‖ ^ 2)
      = fun p => u.gx p ^ 2 + ‖u.gz p‖ ^ 2 := by
    funext p
    show ‖gTildeCd u.gx u.gz (toEuclid m p)‖ ^ 2 = u.gx p ^ 2 + ‖u.gz p‖ ^ 2
    rw [norm_gTildeCd_sq_cd, ofEuclid_toEuclid]
  rw [hfeq]

/-! ## Transport of Rellich–Kondrachov -/

/-- **Rellich–Kondrachov for `H1P Ω` from the Euclidean statement on its image.**  If every
`L²`-bounded sequence in `Weak.H1 (toEuclid m '' Ω)` has an `L²`-convergent subsequence
(`RobinCaps.Compact.RellichEmbeddingL2`), the same holds for `H1P Ω` itself
(`RobinCaps.ThinDomain.RellichEmbeddingP`), for any measurable `Ω ⊆ CapSpace m`. -/
theorem rellichP_of_rellichL2_rth {m : ℕ} {Ω : Set (CapSpace m)} (hΩ : MeasurableSet Ω)
    (hrel : RobinCaps.Compact.RellichEmbeddingL2 (toEuclid m '' Ω)) : RellichEmbeddingP Ω := by
  intro u hbound
  obtain ⟨C, hC⟩ := hbound
  -- Transport the energy bound to the Euclidean sequence.
  have hbound' : ∃ C : ℝ, ∀ k,
      RobinCaps.Sobolev.Weak.dirichlet (transportH1P_cd (u k))
        + RobinCaps.Sobolev.Weak.mass (transportH1P_cd (u k)) ≤ C := by
    refine ⟨C, fun k => ?_⟩
    rw [← dirichletP_eq_dirichlet_transportH1P_rth, ← massP_eq_mass_transportH1P_rth]
    exact hC k
  -- Apply the Euclidean Rellich–Kondrachov hypothesis to the transported sequence.
  obtain ⟨ν, v, hνmono, hvL2, htend⟩ :=
    hrel (fun k => transportH1P_cd (u k)) hbound'
  -- Pull the limit `v` back to `Ω` along `toEuclid m`.
  refine ⟨ν, v ∘ toEuclid m, hνmono, ?_, ?_⟩
  · exact hvL2.comp_measurePreserving (measurePreserving_toEuclid_restrict_cd Ω)
  · have heq : ∀ k, (∫ p in Ω, ((u (ν k)).toFun p - (v ∘ toEuclid m) p) ^ 2)
        = ∫ x in toEuclid m '' Ω, ((transportH1P_cd (u (ν k))).toFun x - v x) ^ 2 := by
      intro k
      rw [setIntegral_toEuclid_image_cd Ω
        (fun x => ((transportH1P_cd (u (ν k))).toFun x - v x) ^ 2)]
      have hfeq : (fun p : CapSpace m =>
            ((transportH1P_cd (u (ν k))).toFun (toEuclid m p) - v (toEuclid m p)) ^ 2)
          = fun p => ((u (ν k)).toFun p - (v ∘ toEuclid m) p) ^ 2 := by
        funext p
        show (((u (ν k)).toFun (ofEuclid m (toEuclid m p))) - v (toEuclid m p)) ^ 2
            = ((u (ν k)).toFun p - v (toEuclid m p)) ^ 2
        rw [ofEuclid_toEuclid]
      rw [hfeq]
    simp_rw [heq]
    exact htend

/-- **Rellich–Kondrachov for the thin domain.**  The specialisation of
`rellichP_of_rellichL2_rth` to `Ω = thinDomain Cm Cp L R`, whose Euclidean image is
(definitionally) `RobinCaps.Sobolev.thinDomainE_cd Cm Cp L R`, and which is open, hence
measurable, under the standard span hypotheses `0 < R` and `(Cm.K + Cp.K) * R < L`. -/
theorem rellichP_thin_rth {m : ℕ} {Cm Cp : Cap m} {L R : ℝ} (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L)
    (hrel : RobinCaps.Compact.RellichEmbeddingL2 (thinDomainE_cd Cm Cp L R)) :
    RellichEmbeddingP (thinDomain Cm Cp L R) :=
  rellichP_of_rellichL2_rth (isOpen_thinDomain hR hL).measurableSet hrel

end RobinCaps.ThinDomain

end
