import RobinCaps.Cap.ShortSliceHemi
import RobinCaps.ThinDomain.BoundaryPieces
import RobinCaps.Sobolev.SphereTraceForm

/-!
# The lateral trace on a general admissible cap, on a sub-interval bounded away from the exit

This file builds the trace operator on the lateral part of the exposed boundary `Γ` of an
**arbitrary** admissible cap `C : Cap m`, in the revolution parametrisation
`(s, ω) ↦ (s, θ(s) • ω)` with `ω` on the unit sphere of `EuclideanSpace ℝ (Fin m)`.  The
construction works uniformly on an axial sub-interval `(-K, a)` where the profile `θ` is bounded
below by `θ(a) > 0` (using `C.θ_antitone`).

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace RobinCaps.Cap

open RobinCaps.ThinDomain RobinCaps.Sobolev RobinCaps.Sobolev.Weak

noncomputable section

variable {m : ℕ}

/-! ## 1. The lateral trace function -/

/-- The lateral trace of `u ∈ H¹(𝒞)` on the surface of revolution, in the parametrisation
`(s, ω) ↦ (s, θ(s) ω)`: at axial level `s` it is the sphere trace of the transverse slice of `u`
on the ball of radius `θ(s)`. -/
def lateralTraceGen_tlg (C : Cap m) (u : H1P C.body) : CapSpace m → ℝ :=
  fun p => if p.1 ∈ Set.Ioo (-C.K) 0 ∧ p.2 ≠ 0 then
    traceSphere (C.θ p.1) (fun z => u.toFun (p.1, z)) (fun z => u.gz (p.1, z)) (‖p.2‖⁻¹ • p.2)
  else 0

/-- The defining identity: on the sphere of radius `θ(s)`, the lateral trace is the sphere trace
of the transverse slice. -/
theorem lateralTraceGen_apply_tlg (C : Cap m) (u : H1P C.body) {s : ℝ}
    (hs : s ∈ Set.Ioo (-C.K) 0) (ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
    lateralTraceGen_tlg C u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
      = traceSphere (C.θ s) (fun z => u.toFun (s, z)) (fun z => u.gz (s, z))
          (ω : EuclideanSpace ℝ (Fin m)) := by
  have hθ : 0 < C.θ s := C.θ_pos s hs
  have hω1 : ‖(ω : EuclideanSpace ℝ (Fin m))‖ = 1 := mem_sphere_zero_iff_norm.1 ω.2
  have hnorm : ‖C.θ s • (ω : EuclideanSpace ℝ (Fin m))‖ = C.θ s := by
    rw [norm_smul, hω1, mul_one, Real.norm_eq_abs, abs_of_pos hθ]
  have hne : C.θ s • (ω : EuclideanSpace ℝ (Fin m)) ≠ 0 := by
    rw [← norm_pos_iff, hnorm]; exact hθ
  simp only [lateralTraceGen_tlg, if_pos (⟨hs, hne⟩ :
    (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))).1 ∈ Set.Ioo (-C.K) 0 ∧
      (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))).2 ≠ 0)]
  rw [hnorm, smul_smul, inv_mul_cancel₀ hθ.ne', one_smul]

/-! ## 2. Measurability -/

/-- **Joint measurability of the lateral trace, modulo the θ-parametrised joint-measurability
sticking point.**

The natural strategy (mirroring `RobinCaps.Cap.aestronglyMeasurable_lateralTraceCyl_tf` in
`RobinCaps/Cap/TraceDataFlat.lean`) is to run `stronglyMeasurable_traceSphere_th` on the globally
strongly measurable representatives `repFun C u`, `repGz_el C u` of `u.toFun`, `u.gz`
(`RobinCaps.Cap.stronglyMeasurable_repFun`, `RobinCaps.Cap.stronglyMeasurable_repGz_el`, both
already available for a general cap `C`), and then transport along the a.e. equalities
`ae_ae_transverse_repFun_el` / `ae_ae_transverse_repGz_el`.  This works verbatim *for each fixed
axial level `s`* (via `RobinCaps.Cap.aestronglyMeasurable_traceSphere_th`, itself proved only for a
fixed radius `R`), but the present theorem needs the *joint* statement in `(s, ω)`.

For the **flat** cap (`RobinCaps/Cap/TraceDataFlat.lean` §3) the joint statement is available
because the radius there is the *constant* `1`, so `RobinCaps.ThinDomain.
stronglyMeasurable_traceSphere_joint_tgb` and `RobinCaps.ThinDomain.ae_radial_congr_joint_tgb`
apply directly.  Here the radius is `C.θ s`, genuinely varying (continuously, not merely
measurably) with `s`: every parametrising integral inside `traceSphere R … w` has `R`-dependent
bounds `R/2 .. R`, so substituting `R = C.θ p.1` turns each integration domain itself into a
function of `p.1`, and the fixed-radius `integral_prod_right'` argument (`stronglyMeasurable_
traceSphere_th`'s proof) does not adapt verbatim; likewise the "joint a.e." argument behind
`ae_radial_congr_joint_tgb` is stated there only for fixed `R`.  We isolate exactly these two
facts — joint strong measurability of the θ-parametrised trace of the canonical measurable
representatives, and its joint a.e. agreement with `lateralTraceGen_tlg` — as explicit hypotheses;
see the accompanying report for the precise open statements. -/
theorem aestronglyMeasurable_lateralTraceGen_tlg (C : Cap m) (u : H1P C.body)
    (hJoint : StronglyMeasurable
        (fun p : ℝ × sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
          traceSphere (C.θ p.1) (fun z => repFun C u (p.1, z)) (fun z => repGz_el C u (p.1, z))
            ((p.2 : EuclideanSpace ℝ (Fin m)))))
    (hJointAE : (fun p : ℝ × sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
          traceSphere (C.θ p.1) (fun z => repFun C u (p.1, z)) (fun z => repGz_el C u (p.1, z))
            ((p.2 : EuclideanSpace ℝ (Fin m))))
        =ᵐ[(volume.restrict (Set.Ioo (-C.K) 0)).prod (sphereMeasure m)]
        (fun p : ℝ × sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
          lateralTraceGen_tlg C u (p.1, C.θ p.1 • ((p.2 : EuclideanSpace ℝ (Fin m)))))) :
    AEStronglyMeasurable
      (fun p : ℝ × sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
        lateralTraceGen_tlg C u (p.1, C.θ p.1 • ((p.2 : EuclideanSpace ℝ (Fin m)))))
      ((volume.restrict (Set.Ioo (-C.K) 0)).prod (sphereMeasure m)) :=
  ⟨_, hJoint, hJointAE.symm⟩

/-! ## 3. The slice-wise trace inequality on a sub-interval with `θ` bounded below -/

/-- A radius-uniform constant for the sphere-trace inequality, valid for every radius
`R ∈ [c, 1]`: `max (4/c · (c/2)^{-(m-1)}) (1 · (c/2)^{-(m-1)})`. -/
def lateralConst_tlg (m : ℕ) (c : ℝ) : ℝ :=
  max (4 / c * ((c / 2) ^ (m - 1))⁻¹) (1 * ((c / 2) ^ (m - 1))⁻¹)

/-- **The radius-uniform bound on `max (4/R·(R/2)^{-(m-1)}) (R·(R/2)^{-(m-1)})` for
`R ∈ [c,1]`.** -/
theorem traceSphereConst_le_lateralConst_tlg {m : ℕ} {c R : ℝ} (hc : 0 < c) (hcR : c ≤ R)
    (hR1 : R ≤ 1) :
    max (4 / R * ((R / 2) ^ (m - 1))⁻¹) (R * ((R / 2) ^ (m - 1))⁻¹) ≤ lateralConst_tlg m c := by
  have hR0 : 0 < R := lt_of_lt_of_le hc hcR
  have hpow : (c / 2) ^ (m - 1) ≤ (R / 2) ^ (m - 1) :=
    pow_le_pow_left₀ (by positivity) (by linarith) (m - 1)
  have hpowc0 : 0 < (c / 2) ^ (m - 1) := by positivity
  have hpowR0 : 0 < (R / 2) ^ (m - 1) := by positivity
  have hinv : ((R / 2) ^ (m - 1))⁻¹ ≤ ((c / 2) ^ (m - 1))⁻¹ := by
    apply inv_anti₀ hpowc0 hpow
  apply max_le
  · have h4 : 4 / R ≤ 4 / c := by
      apply div_le_div_of_nonneg_left (by norm_num) hc hcR
    calc 4 / R * ((R / 2) ^ (m - 1))⁻¹
        ≤ 4 / c * ((R / 2) ^ (m - 1))⁻¹ :=
          mul_le_mul_of_nonneg_right h4 (le_of_lt (inv_pos.2 hpowR0))
      _ ≤ 4 / c * ((c / 2) ^ (m - 1))⁻¹ :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ ≤ lateralConst_tlg m c := le_max_left _ _
  · calc R * ((R / 2) ^ (m - 1))⁻¹
        ≤ 1 * ((R / 2) ^ (m - 1))⁻¹ :=
          mul_le_mul_of_nonneg_right hR1 (le_of_lt (inv_pos.2 hpowR0))
      _ ≤ 1 * ((c / 2) ^ (m - 1))⁻¹ :=
          mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ ≤ lateralConst_tlg m c := le_max_right _ _

/-- **For a.e. axial level `s` in `(-K, a)`, the spherical mean of the squared lateral trace is
controlled by the transverse slice's `H¹` energy, with a constant uniform in `s`.** -/
theorem ae_lateral_sq_le_tlg (C : Cap m) (hm : 1 ≤ m) (u : H1P C.body) {a : ℝ}
    (ha : a ∈ Set.Ioo (-C.K) 0) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioo (-C.K) a)),
      (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
          lateralTraceGen_tlg C u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ^ 2
          ∂(sphereMeasure m))
        ≤ lateralConst_tlg m (C.θ a)
            * ((∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), u.toFun (s, z) ^ 2)
                + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), ‖u.gz (s, z)‖ ^ 2) := by
  have hsub : Set.Ioo (-C.K) a ⊆ Set.Ioo (-C.K) 0 := Set.Ioo_subset_Ioo_right ha.2.le
  have h1 : ∀ᵐ s ∂(volume.restrict (Set.Ioo (-C.K) a)),
      ∃ v : Weak.H1 (ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s)),
        v.toFun = (fun z => u.toFun (s, z)) ∧ v.grad = (fun z => u.gz (s, z)) :=
    ae_restrict_of_ae_restrict_of_subset hsub (ae_transverse_H1_ssh C u)
  have hθc0 : 0 < C.θ a := C.θ_pos a ha
  filter_upwards [h1, ae_restrict_mem measurableSet_Ioo] with s hex hsmem
  obtain ⟨v, hv1, hv2⟩ := hex
  have hsIoo : s ∈ Set.Ioo (-C.K) 0 := hsub hsmem
  have hθs : 0 < C.θ s := C.θ_pos s hsIoo
  have hθs1 : C.θ s ≤ 1 := C.θ_le_one s hsIoo
  have hθc : C.θ a ≤ C.θ s := C.θ_antitone hsIoo ha hsmem.2.le
  have heq1 : (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      lateralTraceGen_tlg C u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ^ 2
      ∂(sphereMeasure m))
      = ∫ w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
          (traceSphere (C.θ s) v.toFun v.grad (w : EuclideanSpace ℝ (Fin m))) ^ 2
          ∂(sphereMeasure m) := by
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only
    rw [lateralTraceGen_apply_tlg C u hsIoo ω, hv1, hv2]
  rw [heq1]
  have hkey := traceSphere_sq_integral_le hm hθs v
  have hmass : Weak.mass v
      = ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), u.toFun (s, z) ^ 2 := by
    rw [Weak.mass, hv1]
  have hdir : Weak.dirichlet v
      = ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), ‖u.gz (s, z)‖ ^ 2 := by
    rw [Weak.dirichlet, hv2]
  rw [hmass, hdir] at hkey
  have hconst := traceSphereConst_le_lateralConst_tlg (m := m) hθc0 hθc hθs1
  have hnn : 0 ≤ (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), u.toFun (s, z) ^ 2)
      + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), ‖u.gz (s, z)‖ ^ 2 := by
    have h1 : 0 ≤ ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), u.toFun (s, z) ^ 2 :=
      integral_nonneg fun _ => sq_nonneg _
    have h2 : 0 ≤ ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), ‖u.gz (s, z)‖ ^ 2 :=
      integral_nonneg fun _ => sq_nonneg _
    linarith
  calc (∫ w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        (traceSphere (C.θ s) v.toFun v.grad (w : EuclideanSpace ℝ (Fin m))) ^ 2
        ∂(sphereMeasure m))
      ≤ max (4 / C.θ s * ((C.θ s / 2) ^ (m - 1))⁻¹) (C.θ s * ((C.θ s / 2) ^ (m - 1))⁻¹)
          * ((∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), u.toFun (s, z) ^ 2)
              + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), ‖u.gz (s, z)‖ ^ 2) := hkey
    _ ≤ lateralConst_tlg m (C.θ a)
          * ((∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), u.toFun (s, z) ^ 2)
              + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), ‖u.gz (s, z)‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hconst hnn

/-! ## 4. The integrated lateral bound on the sub-interval -/

/-- **Fubini for the cap body, in the axial-outer order.** -/
theorem integral_body_eq_integral_axial_slices_tlg (C : Cap m) {f : CapSpace m → ℝ}
    (hf : Integrable (C.body.indicator f) volume) :
    (∫ p in C.body, f p)
      = ∫ s in Set.Ioo (-C.K) 0, ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), f (s, z) := by
  have hf' : Integrable (C.body.indicator f) ((volume : Measure ℝ).prod volume) := by
    rwa [← Measure.volume_eq_prod]
  rw [← integral_indicator (measurableSet_body' C), Measure.volume_eq_prod, integral_prod _ hf',
    ← integral_indicator measurableSet_Ioo]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  by_cases hs : s ∈ Set.Ioo (-C.K) 0
  · rw [indicator_of_mem hs]
    simp only
    rw [← integral_indicator measurableSet_ball]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    exact indicator_body_transverse_el C f hs z
  · rw [indicator_of_notMem hs]
    have hz : ∀ z : EuclideanSpace ℝ (Fin m), (C.body.indicator f) (s, z) = 0 := by
      intro z
      have hnotmem : (s, z) ∉ C.body := fun hmem => hs ⟨hmem.1, hmem.2.1⟩
      exact Set.indicator_of_notMem hnotmem f
    simp [hz]

/-- The axial slice integrals form an integrable function of `s`. -/
theorem integrable_axial_slice_integral_tlg (C : Cap m) {f : CapSpace m → ℝ}
    (hf : Integrable (C.body.indicator f) volume) :
    IntegrableOn (fun s => ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), f (s, z))
      (Set.Ioo (-C.K) 0) volume := by
  have hf' : Integrable (C.body.indicator f) ((volume : Measure ℝ).prod volume) := by
    rwa [← Measure.volume_eq_prod]
  have h0 : Integrable (fun s => ∫ z, (C.body.indicator f) (s, z)) volume :=
    hf'.integral_prod_left
  have heq : (fun s => ∫ z, (C.body.indicator f) (s, z))
      = fun s => (Set.Ioo (-C.K) (0 : ℝ)).indicator
          (fun s => ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), f (s, z)) s := by
    funext s
    by_cases hs : s ∈ Set.Ioo (-C.K) 0
    · rw [indicator_of_mem hs, ← integral_indicator measurableSet_ball]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      exact indicator_body_transverse_el C f hs z
    · rw [indicator_of_notMem hs]
      have hz : ∀ z : EuclideanSpace ℝ (Fin m), (C.body.indicator f) (s, z) = 0 := by
        intro z
        have hnotmem : (s, z) ∉ C.body := fun hmem => hs ⟨hmem.1, hmem.2.1⟩
        exact Set.indicator_of_notMem hnotmem f
      simp [hz]
  rw [heq] at h0
  exact (integrable_indicator_iff measurableSet_Ioo).1 h0

/-- **Bound on the area element via the right derivative at `a`**, valid for a.e. `s ∈ (-K,a)`:
by concavity the right derivative is antitone, so it is bounded (in absolute value, both
derivatives being `≤ 0`) by its value at `a`. -/
theorem ae_capAreaElement_le_tlg (C : Cap m) {a : ℝ} (ha : a ∈ Set.Ioo (-C.K) 0) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioo (-C.K) a)),
      capAreaElement C s ≤ Real.sqrt (1 + (derivWithin C.θ (Set.Ioi a) a) ^ 2) := by
  have hsub : Set.Ioo (-C.K) a ⊆ Set.Ioo (-C.K) 0 := Set.Ioo_subset_Ioo_right ha.2.le
  have hderiv : (fun s => derivWithin C.θ (Set.Ioi s) s)
      =ᵐ[volume.restrict (Set.Ioo (-C.K) 0)] deriv C.θ := Cap.Concave.rightDeriv_ae_eq_deriv C
  have hderiv' : (fun s => derivWithin C.θ (Set.Ioi s) s)
      =ᵐ[volume.restrict (Set.Ioo (-C.K) a)] deriv C.θ :=
    ae_restrict_of_ae_restrict_of_subset hsub hderiv
  filter_upwards [hderiv', ae_restrict_mem measurableSet_Ioo] with s hderivs hsmem
  have hsIoo : s ∈ Set.Ioo (-C.K) 0 := hsub hsmem
  have hsa : s ≤ a := hsmem.2.le
  have hanti := Cap.Concave.antitoneOn_rightDeriv C hsIoo ha hsa
  have hrs0 := Cap.Concave.rightDeriv_nonpos C hsIoo
  have hra0 := Cap.Concave.rightDeriv_nonpos C ha
  have habs : |derivWithin C.θ (Set.Ioi s) s| ≤ |derivWithin C.θ (Set.Ioi a) a| := by
    rw [abs_of_nonpos hrs0, abs_of_nonpos hra0]; linarith
  have hθ1 : C.θ s ≤ 1 := C.θ_le_one s hsIoo
  have hθ0 : 0 < C.θ s := C.θ_pos s hsIoo
  have hpow : C.θ s ^ (m - 1) ≤ 1 := pow_le_one₀ hθ0.le hθ1
  have hpow0 : 0 ≤ C.θ s ^ (m - 1) := by positivity
  have hsq : Real.sqrt (1 + deriv C.θ s ^ 2)
      ≤ Real.sqrt (1 + (derivWithin C.θ (Set.Ioi a) a) ^ 2) := by
    apply Real.sqrt_le_sqrt
    rw [← hderivs]
    nlinarith [sq_abs (derivWithin C.θ (Set.Ioi s) s), sq_abs (derivWithin C.θ (Set.Ioi a) a), habs]
  calc capAreaElement C s = C.θ s ^ (m - 1) * Real.sqrt (1 + deriv C.θ s ^ 2) := rfl
    _ ≤ 1 * Real.sqrt (1 + (derivWithin C.θ (Set.Ioi a) a) ^ 2) :=
        mul_le_mul hpow hsq (Real.sqrt_nonneg _) (by norm_num)
    _ = Real.sqrt (1 + (derivWithin C.θ (Set.Ioi a) a) ^ 2) := one_mul _

/-- The uniform bound `latConstFull_tlg m C a := √(1+rightDeriv(a)²) · lateralConst_tlg m (θ a)`. -/
def latConstFull_tlg (m : ℕ) (C : Cap m) (a : ℝ) : ℝ :=
  Real.sqrt (1 + (derivWithin C.θ (Set.Ioi a) a) ^ 2) * lateralConst_tlg m (C.θ a)

/-- **The integrated lateral bound on the sub-interval `(-K,a)`.** -/
theorem lateral_integral_le_tlg (C : Cap m) (hm : 1 ≤ m) (u : H1P C.body) {a : ℝ}
    (ha : a ∈ Set.Ioo (-C.K) 0) :
    (∫ s in Set.Ioo (-C.K) a, capAreaElement C s
         * ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
             lateralTraceGen_tlg C u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ^ 2
             ∂(sphereMeasure m))
      ≤ latConstFull_tlg m C a * (massP u + dirichletP u) := by
  set A : ℝ := Real.sqrt (1 + (derivWithin C.θ (Set.Ioi a) a) ^ 2) with hAdef
  set Lc : ℝ := lateralConst_tlg m (C.θ a) with hLcdef
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hθa0 : 0 < C.θ a := C.θ_pos a ha
  have hLc0 : 0 ≤ Lc := by
    rw [hLcdef, lateralConst_tlg]
    exact le_trans (by positivity) (le_max_left _ _)
  have hsub : Set.Ioo (-C.K) a ⊆ Set.Ioo (-C.K) 0 := Set.Ioo_subset_Ioo_right ha.2.le
  have hmassOn : IntegrableOn (fun p => u.toFun p ^ 2) C.body volume := u.memL2.integrable_sq
  have hgzOn : IntegrableOn (fun p => ‖u.gz p‖ ^ 2) C.body volume := (u.gz_memL2.norm).integrable_sq
  have hmassInd : Integrable (C.body.indicator fun p => u.toFun p ^ 2) volume :=
    hmassOn.integrable_indicator (measurableSet_body' C)
  have hgzInd : Integrable (C.body.indicator fun p => ‖u.gz p‖ ^ 2) volume :=
    hgzOn.integrable_indicator (measurableSet_body' C)
  -- Fubini identities on the whole domain `(-K,0)`.
  have hmassFub : massP u
      = ∫ s in Set.Ioo (-C.K) 0, ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), u.toFun (s, z) ^ 2 := by
    rw [massP]
    exact integral_body_eq_integral_axial_slices_tlg C hmassInd
  have hgzFub : (∫ p in C.body, ‖u.gz p‖ ^ 2)
      = ∫ s in Set.Ioo (-C.K) 0, ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), ‖u.gz (s, z)‖ ^ 2 :=
    integral_body_eq_integral_axial_slices_tlg C hgzInd
  have hgzle : (∫ p in C.body, ‖u.gz p‖ ^ 2) ≤ dirichletP u := by
    rw [dirichletP]
    have hgxOn : IntegrableOn (fun p => u.gx p ^ 2) C.body volume := u.gx_memL2.integrable_sq
    have hle : ∀ p ∈ C.body, ‖u.gz p‖ ^ 2 ≤ u.gx p ^ 2 + ‖u.gz p‖ ^ 2 := fun p _ => by nlinarith [sq_nonneg (u.gx p)]
    exact setIntegral_mono_on hgzOn (hgxOn.add hgzOn) (measurableSet_body' C) hle
  have hmassInt : IntegrableOn (fun s => ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), u.toFun (s, z) ^ 2)
      (Set.Ioo (-C.K) 0) volume :=
    integrable_axial_slice_integral_tlg C hmassInd
  have hgzInt : IntegrableOn (fun s => ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), ‖u.gz (s, z)‖ ^ 2)
      (Set.Ioo (-C.K) 0) volume :=
    integrable_axial_slice_integral_tlg C hgzInd
  -- The sub-interval bound on the mass and Dirichlet slice integrals.
  have hsubbound : (∫ s in Set.Ioo (-C.K) a,
        ((∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), u.toFun (s, z) ^ 2)
            + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), ‖u.gz (s, z)‖ ^ 2))
      ≤ massP u + dirichletP u := by
    have hmono : (∫ s in Set.Ioo (-C.K) a,
          ((∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), u.toFun (s, z) ^ 2)
              + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), ‖u.gz (s, z)‖ ^ 2))
        ≤ ∫ s in Set.Ioo (-C.K) 0,
          ((∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), u.toFun (s, z) ^ 2)
              + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), ‖u.gz (s, z)‖ ^ 2) := by
      refine setIntegral_mono_set (hmassInt.add hgzInt) ?_ (HasSubset.Subset.eventuallyLE hsub)
      filter_upwards with s
      have h1 : 0 ≤ ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), u.toFun (s, z) ^ 2 :=
        integral_nonneg fun _ => sq_nonneg _
      have h2 : 0 ≤ ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), ‖u.gz (s, z)‖ ^ 2 :=
        integral_nonneg fun _ => sq_nonneg _
      simpa using add_nonneg h1 h2
    rw [integral_add hmassInt hgzInt, ← hmassFub] at hmono
    linarith [hmono, hgzFub, hgzle]
  -- Assemble via the pointwise a.e. bound.
  have hpt : ∀ᵐ s ∂(volume.restrict (Set.Ioo (-C.K) a)),
      capAreaElement C s * (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
          lateralTraceGen_tlg C u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ^ 2 ∂(sphereMeasure m))
        ≤ A * Lc * ((∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), u.toFun (s, z) ^ 2)
            + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), ‖u.gz (s, z)‖ ^ 2) := by
    filter_upwards [ae_capAreaElement_le_tlg C ha, ae_lateral_sq_le_tlg C hm u ha,
      ae_restrict_mem measurableSet_Ioo] with s harea htrace hsmem
    have hθs0 : 0 ≤ C.θ s := (C.θ_pos s (hsub hsmem)).le
    have hcapnn : 0 ≤ capAreaElement C s := by rw [capAreaElement]; positivity
    have htracenn : 0 ≤ ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        lateralTraceGen_tlg C u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ^ 2 ∂(sphereMeasure m) :=
      integral_nonneg fun _ => sq_nonneg _
    calc capAreaElement C s * (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
          lateralTraceGen_tlg C u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ^ 2 ∂(sphereMeasure m))
        ≤ A * (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
            lateralTraceGen_tlg C u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ^ 2 ∂(sphereMeasure m)) :=
          mul_le_mul_of_nonneg_right harea htracenn
      _ ≤ A * (Lc * ((∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), u.toFun (s, z) ^ 2)
            + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), ‖u.gz (s, z)‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left htrace hA0
      _ = A * Lc * ((∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), u.toFun (s, z) ^ 2)
            + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), ‖u.gz (s, z)‖ ^ 2) := by ring
  have hsumInt : IntegrableOn (fun s => (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), u.toFun (s, z) ^ 2)
        + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), ‖u.gz (s, z)‖ ^ 2) (Set.Ioo (-C.K) 0) volume :=
    hmassInt.add hgzInt
  have hmajint : Integrable (fun s => A * Lc * ((∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), u.toFun (s, z) ^ 2)
        + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), ‖u.gz (s, z)‖ ^ 2))
      (volume.restrict (Set.Ioo (-C.K) a)) :=
    (hsumInt.mono_set hsub).const_mul (A * Lc)
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo (-C.K) a)] fun s =>
      capAreaElement C s * (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
          lateralTraceGen_tlg C u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ^ 2 ∂(sphereMeasure m)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hsmem
    have hθs0 : 0 ≤ C.θ s := (C.θ_pos s (hsub hsmem)).le
    have hcapnn : 0 ≤ capAreaElement C s := by rw [capAreaElement]; positivity
    have htracenn : 0 ≤ ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        lateralTraceGen_tlg C u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ^ 2 ∂(sphereMeasure m) :=
      integral_nonneg fun _ => sq_nonneg _
    exact mul_nonneg hcapnn htracenn
  have hstep := integral_mono_of_nonneg hnn hmajint hpt
  rw [integral_const_mul] at hstep
  calc (∫ s in Set.Ioo (-C.K) a, capAreaElement C s
        * ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
            lateralTraceGen_tlg C u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ^ 2
            ∂(sphereMeasure m))
      ≤ A * Lc * (∫ s in Set.Ioo (-C.K) a,
          ((∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), u.toFun (s, z) ^ 2)
              + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), ‖u.gz (s, z)‖ ^ 2)) := hstep
    _ ≤ A * Lc * (massP u + dirichletP u) :=
        mul_le_mul_of_nonneg_left hsubbound (by positivity)
    _ = latConstFull_tlg m C a * (massP u + dirichletP u) := by rw [latConstFull_tlg]

/-! ## 5. Consistency with a continuous representative -/

/-- Every point `(s,z)` with `s ∈ (-K,0)` and `‖z‖ ≤ θ(s)` lies in the closure of the body: it is
approached from inside along the segment `t ↦ (s, t z)`, `t ↑ 1`. -/
theorem radialPt_mem_closure_body_tlg (C : Cap m) {s : ℝ} (hs : s ∈ Set.Ioo (-C.K) 0)
    {z : EuclideanSpace ℝ (Fin m)} (hz : ‖z‖ ≤ C.θ s) :
    (s, z) ∈ closure C.body := by
  set f : ℝ → CapSpace m := fun t => (s, t • z) with hfdef
  have hcont : Continuous f :=
    Continuous.prodMk continuous_const (continuous_id.smul continuous_const)
  have hf1 : f 1 = (s, z) := by simp [hfdef]
  have htend : Tendsto f (𝓝[<] (1 : ℝ)) (𝓝 (s, z)) := by
    rw [← hf1]
    exact (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto htend ?_
  have h0 : ∀ᶠ t in 𝓝[<] (1 : ℝ), (0 : ℝ) < t :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [h0, self_mem_nhdsWithin] with t ht0 ht1
  have ht1' : t < 1 := ht1
  refine ⟨hs.1, hs.2, ?_⟩
  show ‖t • z‖ < C.θ s
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
  have hθ := C.θ_pos s hs
  nlinarith [norm_nonneg z]

/-- **Consistency with a continuous representative.**  If `u.toFun` is continuous on the closure
of the body, the lateral trace agrees a.e. with the pointwise boundary values. -/
theorem lateralTraceGen_eq_of_continuousOn_tlg (C : Cap m) (hm : 1 ≤ m) (u : H1P C.body)
    (hcont : ContinuousOn u.toFun (closure C.body)) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioo (-C.K) 0)),
      ∀ᵐ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 ∂(sphereMeasure m),
      lateralTraceGen_tlg C u (s, C.θ s • ((ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
        EuclideanSpace ℝ (Fin m)))
        = u.toFun (s, C.θ s • ((ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
          EuclideanSpace ℝ (Fin m))) := by
  filter_upwards [ae_transverse_H1_ssh C u, ae_restrict_mem measurableSet_Ioo] with s hex hsmem
  obtain ⟨v, hv1, hv2⟩ := hex
  have hθs : 0 < C.θ s := C.θ_pos s hsmem
  have hcont' : ∀ w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      ContinuousOn (fun r : ℝ => v.toFun (r • (w : EuclideanSpace ℝ (Fin m))))
        (Icc (C.θ s / 2) (C.θ s)) := by
    intro w
    have heq : (fun r : ℝ => v.toFun (r • (w : EuclideanSpace ℝ (Fin m))))
        = u.toFun ∘ (fun r : ℝ => (s, r • (w : EuclideanSpace ℝ (Fin m)))) := by
      funext r; rw [hv1]; rfl
    rw [heq]
    refine hcont.comp
      (Continuous.continuousOn
        (Continuous.prodMk continuous_const (continuous_id.smul continuous_const))) ?_
    intro r hr
    refine radialPt_mem_closure_body_tlg C hsmem ?_
    rw [norm_smul, mem_sphere_zero_iff_norm.1 w.2, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (le_trans (by linarith [hθs] : (0 : ℝ) ≤ C.θ s / 2) hr.1)]
    exact hr.2
  have hkey := traceSphere_eq_of_continuousOn_th hm hθs v hcont'
  filter_upwards [hkey] with w hw
  rw [lateralTraceGen_apply_tlg C u hsmem w, ← hv1, ← hv2, hw, hv1]

/-! ## 6. Linearity (a.e.) -/

/-- **Additivity of the lateral trace (a.e.).** -/
theorem lateralTraceGen_add_tlg (C : Cap m) (hm : 1 ≤ m) (u v : H1P C.body) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioo (-C.K) 0)),
      ∀ᵐ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 ∂(sphereMeasure m),
      lateralTraceGen_tlg C (u + v) (s, C.θ s • ((ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
          EuclideanSpace ℝ (Fin m)))
        = lateralTraceGen_tlg C u (s, C.θ s • ((ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
            EuclideanSpace ℝ (Fin m)))
          + lateralTraceGen_tlg C v (s, C.θ s • ((ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
              EuclideanSpace ℝ (Fin m))) := by
  filter_upwards [ae_transverse_H1_ssh C u, ae_transverse_H1_ssh C v,
    ae_restrict_mem measurableSet_Ioo] with s hexu hexv hsmem
  obtain ⟨vu, hvu1, hvu2⟩ := hexu
  obtain ⟨vv, hvv1, hvv2⟩ := hexv
  have hθs : 0 < C.θ s := C.θ_pos s hsmem
  have heqfun : (fun z => (u + v).toFun (s, z)) = (vu + vv).toFun := by
    rw [Weak.H1.add_toFun, H1P.add_toFun]
    funext z; simp [Pi.add_apply, hvu1, hvv1]
  have heqgrad : (fun z => (u + v).gz (s, z)) = (vu + vv).grad := by
    rw [Weak.H1.add_grad, H1P.add_gz]
    funext z; simp [Pi.add_apply, hvu2, hvv2]
  have hkey := traceSphere_add_ae_stf hm hθs vu vv
  filter_upwards [hkey] with ω hω
  rw [lateralTraceGen_apply_tlg C (u + v) hsmem ω, lateralTraceGen_apply_tlg C u hsmem ω,
    lateralTraceGen_apply_tlg C v hsmem ω, heqfun, heqgrad, hω, hvu1, hvu2, hvv1, hvv2]

/-- **Scalar homogeneity of the lateral trace (a.e.).** -/
theorem lateralTraceGen_smul_tlg (C : Cap m) (c : ℝ) (u : H1P C.body) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioo (-C.K) 0)),
      ∀ᵐ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 ∂(sphereMeasure m),
      lateralTraceGen_tlg C (c • u) (s, C.θ s • ((ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
          EuclideanSpace ℝ (Fin m)))
        = c * lateralTraceGen_tlg C u (s, C.θ s • ((ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
            EuclideanSpace ℝ (Fin m))) := by
  filter_upwards [ae_transverse_H1_ssh C u, ae_restrict_mem measurableSet_Ioo] with s hexu hsmem
  obtain ⟨vu, hvu1, hvu2⟩ := hexu
  have hθs : 0 < C.θ s := C.θ_pos s hsmem
  have heqfun : (fun z => (c • u).toFun (s, z)) = (c • vu).toFun := by
    rw [Weak.H1.smul_toFun, H1P.smul_toFun]
    funext z; simp [Pi.smul_apply, hvu1, smul_eq_mul]
  have heqgrad : (fun z => (c • u).gz (s, z)) = (c • vu).grad := by
    rw [Weak.H1.smul_grad, H1P.smul_gz]
    funext z; simp [Pi.smul_apply, hvu2]
  filter_upwards with ω
  rw [lateralTraceGen_apply_tlg C (c • u) hsmem ω, lateralTraceGen_apply_tlg C u hsmem ω,
    heqfun, heqgrad, traceSphere_smul_stf, hvu1, hvu2]

end
end RobinCaps.Cap
