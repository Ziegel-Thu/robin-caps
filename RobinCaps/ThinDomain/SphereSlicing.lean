import RobinCaps.ThinDomain.BoundaryPieces
import RobinCaps.Domain.CapsuleThin

/-!
# Slicing mathlib's sphere measure by the height coordinate

Write `σ_k = sphereMeasure k = (volume : Measure (EuclideanSpace ℝ (Fin k))).toSphere` for the
unnormalised surface measure of the unit sphere of `ℝ^k` (`RobinCaps.ThinDomain.Polar`), so that
`σ_{m+1}` lives on `S^m ⊂ ℝ^{m+1}` and has total mass `(m+1) ω_{m+1}`.

The main result is the **height slicing formula**: for `m ≥ 1`,

`∫_{S^m} f dσ_{m+1} = ∫_{-1}^{1} (1-t²)^{(m-2)/2} (∫_{S^{m-1}} f(t, √(1-t²) ω') dσ_m(ω')) dt`,

where the point of `S^m` at height `t` with transverse direction `ω'` is
`heightPoint m t ω' = toEuclid m (t, √(1-t²) • ω')` (`RobinCaps.Domain.toEuclid`, i.e.
`Fin.cons`, so its `0`-th coordinate is `t` and its `Fin.tail` is `√(1-t²) ω'`).

* `sliceDensity m t = (1-t²)^{(m-2)/2}` is the slicing density (a real `rpow`, so the
  formula is uniform in `m ≥ 1`; for `m = 1` the exponent is `-1/2`);
* `lintegral_sphere_slicing` is the `lintegral` form, `integral_sphere_slicing` the Bochner form;
* `map_heightSplit` is the underlying identity of measures,
  `(heightMeasure m).prod σ_m ∘ heightSplit⁻¹ = σ_{m+1}`;
* `sphereSlice_total_mass` is the sanity check obtained from `f = 1`;
* `capLateralIntegral_hemisphere_eq` identifies the project's lateral boundary integral of the
  hemispherical end cap with the sphere-measure integral over the open upper half-sphere.

The proof goes through polar coordinates twice: `lintegral_polar` in `ℝ^{m+1}` on one side, and
Fubini for `ℝ^{m+1} = ℝ × ℝ^m` followed by `lintegral_polar` in `ℝ^m` and two-dimensional polar
coordinates in the `(t, ρ)` half-plane (mathlib's `lintegral_comp_polarCoord_symm`) on the other;
the angular variable is then turned into the height by the substitution `t = cos φ`
(`lintegral_image_eq_lintegral_abs_deriv_mul`).  A fixed radial bump separates the two.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Metric Set Module Filter
open scoped ENNReal NNReal

noncomputable section

namespace RobinCaps.ThinDomain

open RobinCaps.Domain

/-! ## The slicing density -/

/-- The height-slicing density `(1-t²)^{(m-2)/2}` for the unit sphere of `ℝ^{m+1}`. -/
def sliceDensity (m : ℕ) (t : ℝ) : ℝ := (1 - t ^ 2) ^ (((m : ℝ) - 2) / 2)

theorem measurable_sliceDensity (m : ℕ) : Measurable (sliceDensity m) :=
  Measurable.pow (measurable_const.sub (measurable_id.pow_const 2)) measurable_const

theorem measurable_ofReal_sliceDensity (m : ℕ) :
    Measurable fun t : ℝ => ENNReal.ofReal (sliceDensity m t) :=
  ENNReal.measurable_ofReal.comp (measurable_sliceDensity m)

theorem sliceDensity_pos (m : ℕ) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) : 0 < sliceDensity m t := by
  have h : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  exact Real.rpow_pos_of_pos h _

theorem sliceDensity_nonneg (m : ℕ) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    0 ≤ sliceDensity m t := (sliceDensity_pos m ht).le

/-- On `(0, π)` the slicing density composed with `cos` collapses: `sin φ · (sin²φ)^{(m-2)/2}
= sin^{m-1} φ`. -/
theorem sin_mul_sliceDensity_cos (m : ℕ) (hm : 1 ≤ m) {φ : ℝ} (hφ : φ ∈ Ioo (0 : ℝ) Real.pi) :
    Real.sin φ * sliceDensity m (Real.cos φ) = Real.sin φ ^ (m - 1) := by
  have hs : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ.1 hφ.2
  have hcos : 1 - Real.cos φ ^ 2 = Real.sin φ ^ 2 := by
    have := Real.sin_sq_add_cos_sq φ; linarith
  rw [sliceDensity, hcos]
  have h1 : (Real.sin φ ^ 2 : ℝ) ^ (((m : ℝ) - 2) / 2) = Real.sin φ ^ ((m : ℝ) - 2) := by
    rw [← Real.rpow_natCast (Real.sin φ) 2, ← Real.rpow_mul hs.le]
    congr 1
    push_cast
    ring
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    have := Nat.cast_sub (R := ℝ) hm
    simpa using this
  rw [h1, ← Real.rpow_natCast (Real.sin φ) (m - 1), hcast,
    show (m : ℝ) - 1 = 1 + ((m : ℝ) - 2) by ring, Real.rpow_add hs, Real.rpow_one]

/-! ## The image of `cos` and the substitution `u = cos φ` -/

theorem cos_image_Ioo : Real.cos '' (Ioo (0 : ℝ) Real.pi) = Ioo (-1 : ℝ) 1 := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hx1 : x ∈ Icc (0 : ℝ) Real.pi := ⟨hx.1.le, hx.2.le⟩
    constructor
    · have := Real.strictAntiOn_cos hx1 ⟨Real.pi_pos.le, le_refl _⟩ hx.2
      simpa using this
    · have := Real.strictAntiOn_cos ⟨le_refl (0:ℝ), Real.pi_pos.le⟩ hx1 hx.1
      simpa using this
  · intro u hu
    refine ⟨Real.arccos u, ⟨?_, ?_⟩, Real.cos_arccos hu.1.le hu.2.le⟩
    · exact Real.arccos_pos.2 hu.2
    · rcases lt_or_ge (Real.arccos u) Real.pi with h | h
      · exact h
      · exfalso
        have hle : Real.arccos u ≤ Real.pi := Real.arccos_le_pi u
        have heq : Real.arccos u = Real.pi := le_antisymm hle h
        have : u = -1 := by
          have := Real.cos_arccos hu.1.le hu.2.le
          rw [heq, Real.cos_pi] at this
          exact this.symm
        exact absurd this (by intro h'; rw [h'] at hu; exact absurd hu.1 (lt_irrefl _))

/-- The substitution `u = cos φ` in the slicing integral. -/
theorem lintegral_sliceDensity_eq_sin (m : ℕ) (hm : 1 ≤ m) (Φ : ℝ → ℝ → ℝ≥0∞) :
    ∫⁻ u in Ioo (-1 : ℝ) 1,
        ENNReal.ofReal (sliceDensity m u) * Φ u (Real.sqrt (1 - u ^ 2))
      = ∫⁻ φ in Ioo (0 : ℝ) Real.pi,
          ENNReal.ofReal (Real.sin φ ^ (m - 1)) * Φ (Real.cos φ) (Real.sin φ) := by
  rw [← cos_image_Ioo,
    MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
      (f := Real.cos) (f' := fun φ => -Real.sin φ)
      (fun x _ => (Real.hasDerivAt_cos x).hasDerivWithinAt)
      (Real.injOn_cos.mono Set.Ioo_subset_Icc_self)]
  refine setLIntegral_congr_fun measurableSet_Ioo (fun φ hφ => ?_)
  have hs : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ.1 hφ.2
  have hcos : 1 - Real.cos φ ^ 2 = Real.sin φ ^ 2 := by
    have := Real.sin_sq_add_cos_sq φ; linarith
  rw [hcos, Real.sqrt_sq hs.le, abs_neg, abs_of_nonneg hs.le, ← mul_assoc,
    ← ENNReal.ofReal_mul hs.le, sin_mul_sliceDensity_cos m hm hφ]

/-! ## Polar coordinates in the upper half plane -/

/-- Shrinking the domain of a `lintegral` to a subset off which the integrand vanishes. -/
theorem setLIntegral_eq_of_vanish {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t) (hts : t ⊆ s)
    {f : α → ℝ≥0∞} (h0 : ∀ x ∈ s, x ∉ t → f x = 0) :
    ∫⁻ x in s, f x ∂μ = ∫⁻ x in t, f x ∂μ := by
  rw [← lintegral_indicator hs, ← lintegral_indicator ht]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ t
  · rw [Set.indicator_of_mem (hts hx), Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx]
    by_cases hx' : x ∈ s
    · rw [Set.indicator_of_mem hx', h0 x hx' hx]
    · rw [Set.indicator_of_notMem hx']

/-- **Polar coordinates in the upper half plane**: for an integrand supported in
`{(t,ρ) : ρ > 0}` the plane integral becomes an integral over `(0,∞) × (0,π)`. -/
theorem lintegral_upper_halfplane {K : ℝ × ℝ → ℝ≥0∞}
    (hK0 : ∀ p : ℝ × ℝ, p.2 ≤ 0 → K p = 0) :
    ∫⁻ p, K p ∂(volume : Measure (ℝ × ℝ))
      = ∫⁻ p in (Ioi (0 : ℝ)) ×ˢ (Ioo (0 : ℝ) Real.pi),
          ENNReal.ofReal p.1 * K (p.1 * Real.cos p.2, p.1 * Real.sin p.2) := by
  rw [← lintegral_comp_polarCoord_symm K]
  have htarget : polarCoord.target = (Ioi (0 : ℝ)) ×ˢ (Ioo (-Real.pi) Real.pi) := rfl
  rw [htarget]
  refine setLIntegral_eq_of_vanish (measurableSet_Ioi.prod measurableSet_Ioo)
    (measurableSet_Ioi.prod measurableSet_Ioo)
    (Set.prod_mono_right (Set.Ioo_subset_Ioo (by linarith [Real.pi_pos]) le_rfl))
    (fun p hp hp' => ?_)
  have hr : 0 < p.1 := hp.1
  have hφ : p.2 ∈ Ioo (-Real.pi) Real.pi := hp.2
  have hle : p.2 ≤ 0 := by
    by_contra h
    exact hp' ⟨hr, not_le.1 h, hφ.2⟩
  have hsin : Real.sin p.2 ≤ 0 := Real.sin_nonpos_of_nonpos_of_neg_pi_le hle hφ.1.le
  have : K (polarCoord.symm p) = 0 := by
    refine hK0 _ ?_
    show p.1 * Real.sin p.2 ≤ 0
    exact mul_nonpos_of_nonneg_of_nonpos hr.le hsin
  rw [smul_eq_mul, this, mul_zero]

/-- Tonelli on a product set of the plane. -/
theorem lintegral_prod_set {g : ℝ × ℝ → ℝ≥0∞} (hg : Measurable g) (s t : Set ℝ) :
    ∫⁻ p in s ×ˢ t, g p ∂(volume : Measure (ℝ × ℝ))
      = ∫⁻ r in s, ∫⁻ φ in t, g (r, φ) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hg.aemeasurable]

/-! ## The height parametrisation of the sphere -/

variable {m : ℕ}

/-- The point of the unit sphere of `ℝ^{m+1}` with height `t` and transverse direction `ω`. -/
def heightPoint (m : ℕ) (t : ℝ) (ω : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin (m + 1)) :=
  toEuclid m (t, Real.sqrt (1 - t ^ 2) • ω)

theorem smul_toEuclid (r : ℝ) (p : CapSpace m) :
    r • toEuclid m p = toEuclid m (r * p.1, r • p.2) := by
  refine PiLp.ext fun j => ?_
  refine Fin.cases ?_ ?_ j
  · simp [toEuclid]
  · intro i; simp [toEuclid]

theorem smul_heightPoint (r t : ℝ) (ω : EuclideanSpace ℝ (Fin m)) :
    r • heightPoint m t ω = toEuclid m (r * t, (r * Real.sqrt (1 - t ^ 2)) • ω) := by
  rw [heightPoint, smul_toEuclid, smul_smul]

theorem norm_heightPoint {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1)
    {ω : EuclideanSpace ℝ (Fin m)} (hω : ‖ω‖ = 1) : ‖heightPoint m t ω‖ = 1 := by
  have h0 : (0 : ℝ) ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  have hsq : ‖heightPoint m t ω‖ ^ 2 = 1 := by
    rw [heightPoint, norm_toEuclid_sq]
    simp only [norm_smul, Real.norm_eq_abs, hω, mul_one,
      abs_of_nonneg (Real.sqrt_nonneg (1 - t ^ 2))]
    rw [Real.sq_sqrt h0]
    ring
  calc ‖heightPoint m t ω‖
      = Real.sqrt (‖heightPoint m t ω‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = 1 := by rw [hsq, Real.sqrt_one]

@[simp] theorem heightPoint_apply_zero (m : ℕ) (t : ℝ) (ω : EuclideanSpace ℝ (Fin m)) :
    heightPoint m t ω 0 = t := rfl

theorem ofEuclid_heightPoint (m : ℕ) (t : ℝ) (ω : EuclideanSpace ℝ (Fin m)) :
    (ofEuclid m (heightPoint m t ω)).2 = Real.sqrt (1 - t ^ 2) • ω := by
  rw [heightPoint, ofEuclid_toEuclid]

/-- The transverse part used throughout is the `Fin.tail` of the coordinate vector. -/
theorem ofEuclid_snd_eq_tail (m : ℕ) (x : EuclideanSpace ℝ (Fin (m + 1))) :
    (ofEuclid m x).2 = WithLp.toLp 2 (Fin.tail (WithLp.ofLp x)) := rfl

theorem measurable_heightPoint (m : ℕ) :
    Measurable fun p : ℝ × EuclideanSpace ℝ (Fin m) => heightPoint m p.1 p.2 := by
  refine (measurable_toEuclid m).comp (Measurable.prodMk measurable_fst ?_)
  exact Measurable.smul
    ((Real.continuous_sqrt.measurable).comp (measurable_const.sub (measurable_fst.pow_const 2)))
    measurable_snd

/-! ## The two polar reductions of an integral over `ℝ^{m+1}` -/

/-- Fubini for `ℝ^{m+1} = ℝ × ℝ^m` followed by polar coordinates in the transverse factor. -/
theorem lintegral_euclid_split (m : ℕ) (hm : 1 ≤ m)
    {F : EuclideanSpace ℝ (Fin (m + 1)) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂(volume : Measure (EuclideanSpace ℝ (Fin (m + 1))))
      = ∫⁻ t : ℝ, ∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal (ρ ^ (m - 1)) *
          ∫⁻ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
            F (toEuclid m (t, ρ • (ω : EuclideanSpace ℝ (Fin m)))) ∂(sphereMeasure m) := by
  haveI := nontrivial_euclidean hm
  rw [← (measurePreserving_toEuclid m).lintegral_comp hF, Measure.volume_eq_prod,
    lintegral_prod (fun p : ℝ × EuclideanSpace ℝ (Fin m) => F (toEuclid m p))
      (hF.comp (measurable_toEuclid m)).aemeasurable]
  refine lintegral_congr fun t => ?_
  have h := lintegral_polar (volume : Measure (EuclideanSpace ℝ (Fin m)))
    (fun z => F (toEuclid m (t, z)))
    (hF.comp ((measurable_toEuclid m).comp (measurable_const.prodMk measurable_id)))
  rw [finrank_eq] at h
  exact h

/-- **Polar coordinates through the height parametrisation.**  The integral over `ℝ^{m+1}` in
the coordinates `x = r · (t, √(1-t²) ω)`. -/
theorem lintegral_height_polar (m : ℕ) (hm : 1 ≤ m)
    {F : EuclideanSpace ℝ (Fin (m + 1)) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂(volume : Measure (EuclideanSpace ℝ (Fin (m + 1))))
      = ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ m) *
          ∫⁻ u in Ioo (-1 : ℝ) 1, ENNReal.ofReal (sliceDensity m u) *
            ∫⁻ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
              F (r • heightPoint m u (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m) := by
  classical
  set Hf : ℝ → ℝ → ℝ≥0∞ := fun t ρ =>
    ∫⁻ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      F (toEuclid m (t, ρ • (ω : EuclideanSpace ℝ (Fin m)))) ∂(sphereMeasure m) with hHfdef
  have hHf : Measurable fun p : ℝ × ℝ => Hf p.1 p.2 := by
    rw [hHfdef]
    exact Measurable.lintegral_prod_right' (ν := sphereMeasure m)
      (f := fun q : (ℝ × ℝ) × sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
        F (toEuclid m (q.1.1, q.1.2 • (q.2 : EuclideanSpace ℝ (Fin m)))))
      (hF.comp ((measurable_toEuclid m).comp (Measurable.prodMk measurable_fst.fst
        ((measurable_fst.snd).smul (measurable_subtype_coe.comp measurable_snd)))))
  set K : ℝ × ℝ → ℝ≥0∞ :=
    (Prod.snd ⁻¹' (Ioi (0 : ℝ))).indicator
      (fun q : ℝ × ℝ => ENNReal.ofReal (q.2 ^ (m - 1)) * Hf q.1 q.2) with hKdef
  have hset : MeasurableSet (Prod.snd ⁻¹' (Ioi (0 : ℝ)) : Set (ℝ × ℝ)) :=
    (measurable_snd : Measurable (Prod.snd : ℝ × ℝ → ℝ)) measurableSet_Ioi
  have hKmeas : Measurable K :=
    Measurable.indicator
      ((ENNReal.measurable_ofReal.comp (measurable_snd.pow_const _)).mul hHf) hset
  have hKzero : ∀ p : ℝ × ℝ, p.2 ≤ 0 → K p = 0 := by
    intro p hp
    exact Set.indicator_of_notMem (show (p : ℝ × ℝ) ∉ Prod.snd ⁻¹' (Ioi (0 : ℝ)) by
      simpa using hp) _
  have hKslice : ∀ t : ℝ, ∫⁻ ρ, K (t, ρ)
      = ∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal (ρ ^ (m - 1)) * Hf t ρ := by
    intro t
    rw [← lintegral_indicator measurableSet_Ioi]
    refine lintegral_congr fun ρ => ?_
    by_cases hρ : (0 : ℝ) < ρ
    · rw [hKdef,
        Set.indicator_of_mem (show ((t, ρ) : ℝ × ℝ) ∈ Prod.snd ⁻¹' (Ioi (0 : ℝ)) from hρ),
        Set.indicator_of_mem (show ρ ∈ Ioi (0 : ℝ) from hρ)]
    · rw [hKdef,
        Set.indicator_of_notMem (show ((t, ρ) : ℝ × ℝ) ∉ Prod.snd ⁻¹' (Ioi (0 : ℝ)) from hρ),
        Set.indicator_of_notMem (show ρ ∉ Ioi (0 : ℝ) from hρ)]
  calc ∫⁻ x, F x ∂(volume : Measure (EuclideanSpace ℝ (Fin (m + 1))))
      = ∫⁻ t : ℝ, ∫⁻ ρ, K (t, ρ) := by
        rw [lintegral_euclid_split m hm hF]
        exact (lintegral_congr fun t => hKslice t).symm
    _ = ∫⁻ p, K p ∂(volume : Measure (ℝ × ℝ)) := by
        rw [Measure.volume_eq_prod, lintegral_prod _ hKmeas.aemeasurable]
    _ = ∫⁻ p in (Ioi (0 : ℝ)) ×ˢ (Ioo (0 : ℝ) Real.pi),
          ENNReal.ofReal p.1 * K (p.1 * Real.cos p.2, p.1 * Real.sin p.2) :=
        lintegral_upper_halfplane hKzero
    _ = ∫⁻ r in Ioi (0 : ℝ), ∫⁻ φ in Ioo (0 : ℝ) Real.pi,
          ENNReal.ofReal r * K (r * Real.cos φ, r * Real.sin φ) := by
        refine lintegral_prod_set ?_ _ _
        exact (ENNReal.measurable_ofReal.comp measurable_fst).mul (hKmeas.comp
          (Measurable.prodMk (measurable_fst.mul (Real.continuous_cos.measurable.comp
              measurable_snd))
            (measurable_fst.mul (Real.continuous_sin.measurable.comp measurable_snd))))
    _ = ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ m) *
          ∫⁻ u in Ioo (-1 : ℝ) 1, ENNReal.ofReal (sliceDensity m u) *
            Hf (r * u) (r * Real.sqrt (1 - u ^ 2)) := by
        refine setLIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
        have hr0 : (0 : ℝ) < r := hr
        rw [lintegral_sliceDensity_eq_sin m hm (fun u v => Hf (r * u) (r * v))]
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine setLIntegral_congr_fun measurableSet_Ioo (fun φ hφ => ?_)
        have hs : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ.1 hφ.2
        have hmem : (0 : ℝ) < r * Real.sin φ := mul_pos hr0 hs
        rw [hKdef,
          Set.indicator_of_mem
            (show ((r * Real.cos φ, r * Real.sin φ) : ℝ × ℝ) ∈ Prod.snd ⁻¹' (Ioi (0 : ℝ))
              from hmem)]
        rw [← mul_assoc, ← ENNReal.ofReal_mul hr0.le, ← mul_assoc,
          ← ENNReal.ofReal_mul (pow_nonneg hr0.le m)]
        have hpow : r * r ^ (m - 1) = r ^ m := by
          rw [← pow_succ']
          congr 1
          omega
        congr 2
        calc r * (r * Real.sin φ) ^ (m - 1)
            = (r * r ^ (m - 1)) * Real.sin φ ^ (m - 1) := by rw [mul_pow]; ring
          _ = r ^ m * Real.sin φ ^ (m - 1) := by rw [hpow]
    _ = _ := by
        refine setLIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
        congr 1
        refine setLIntegral_congr_fun measurableSet_Ioo (fun u _ => ?_)
        congr 1
        refine lintegral_congr fun ω => ?_
        rw [smul_heightPoint]

/-! ## The slicing identity for the sphere measure -/

/-- The bump used to separate the radial variable: the indicator of `(1,2)`. -/
private def radialBump : ℝ → ℝ≥0∞ := (Ioo (1 : ℝ) 2).indicator (fun _ => 1)

private theorem measurable_radialBump : Measurable radialBump :=
  measurable_const.indicator measurableSet_Ioo

private theorem measurable_radialWeight (m : ℕ) :
    Measurable fun r : ℝ => ENNReal.ofReal (r ^ m) * radialBump r :=
  (ENNReal.measurable_ofReal.comp (measurable_id.pow_const m)).mul measurable_radialBump

private theorem radialBump_ne_top (r : ℝ) : radialBump r ≠ ⊤ := by
  by_cases h : r ∈ Ioo (1 : ℝ) 2
  · rw [radialBump, Set.indicator_of_mem h]; exact ENNReal.one_ne_top
  · rw [radialBump, Set.indicator_of_notMem h]; exact ENNReal.zero_ne_top

private theorem radialBump_integral_pos (m : ℕ) :
    (1 : ℝ≥0∞) ≤ ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ m) * radialBump r := by
  have hpt : EqOn (fun r : ℝ => ENNReal.ofReal (r ^ m) * radialBump r)
      ((Ioo (1 : ℝ) 2).indicator (fun r : ℝ => ENNReal.ofReal (r ^ m))) (Ioi (0 : ℝ)) := by
    intro r _
    show ENNReal.ofReal (r ^ m) * radialBump r
      = (Ioo (1 : ℝ) 2).indicator (fun r : ℝ => ENNReal.ofReal (r ^ m)) r
    by_cases h : r ∈ Ioo (1 : ℝ) 2
    · rw [radialBump, Set.indicator_of_mem h, Set.indicator_of_mem h, mul_one]
    · rw [radialBump, Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt, lintegral_indicator measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo,
    Set.inter_eq_self_of_subset_left
      (show Ioo (1 : ℝ) 2 ⊆ Ioi (0 : ℝ) from fun x hx => lt_trans zero_lt_one hx.1)]
  calc (1 : ℝ≥0∞) = ∫⁻ _ in Ioo (1 : ℝ) 2, (1 : ℝ≥0∞) := by
        rw [setLIntegral_const, Real.volume_Ioo]
        norm_num
    _ ≤ _ := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
        exact ENNReal.one_le_ofReal.2 (one_le_pow₀ hr.1.le)

private theorem radialBump_integral_lt_top (m : ℕ) :
    (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ m) * radialBump r) ≠ ⊤ := by
  have hpt : EqOn (fun r : ℝ => ENNReal.ofReal (r ^ m) * radialBump r)
      ((Ioo (1 : ℝ) 2).indicator (fun r : ℝ => ENNReal.ofReal (r ^ m))) (Ioi (0 : ℝ)) := by
    intro r _
    show ENNReal.ofReal (r ^ m) * radialBump r
      = (Ioo (1 : ℝ) 2).indicator (fun r : ℝ => ENNReal.ofReal (r ^ m)) r
    by_cases h : r ∈ Ioo (1 : ℝ) 2
    · rw [radialBump, Set.indicator_of_mem h, Set.indicator_of_mem h, mul_one]
    · rw [radialBump, Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt, lintegral_indicator measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo,
    Set.inter_eq_self_of_subset_left
      (show Ioo (1 : ℝ) 2 ⊆ Ioi (0 : ℝ) from fun x hx => lt_trans zero_lt_one hx.1)]
  have hle : (∫⁻ r in Ioo (1 : ℝ) 2, ENNReal.ofReal (r ^ m))
      ≤ ENNReal.ofReal ((2 : ℝ) ^ m) := by
    calc (∫⁻ r in Ioo (1 : ℝ) 2, ENNReal.ofReal (r ^ m))
        ≤ ∫⁻ _ in Ioo (1 : ℝ) 2, ENNReal.ofReal ((2 : ℝ) ^ m) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
          exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by linarith [hr.1]) hr.2.le m)
      _ = ENNReal.ofReal ((2 : ℝ) ^ m) * volume (Ioo (1 : ℝ) 2) := setLIntegral_const _ _
      _ = ENNReal.ofReal ((2 : ℝ) ^ m) := by rw [Real.volume_Ioo]; norm_num
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

/-- **The slicing formula for mathlib's sphere measure** (`lintegral` form).

For a measurable `g : ℝ^{m+1} → ℝ≥0∞`,
`∫_{S^m} g dσ_m = ∫_{-1}^{1} (1-t²)^{(m-2)/2} (∫_{S^{m-1}} g(t, √(1-t²) ω') dσ_{m-1}(ω')) dt`,
where the point of `S^m` at height `t` and transverse direction `ω'` is
`heightPoint m t ω' = toEuclid m (t, √(1-t²) • ω')` (so its `0`-th coordinate is `t`). -/
theorem lintegral_sphere_slicing (m : ℕ) (hm : 1 ≤ m)
    {g : EuclideanSpace ℝ (Fin (m + 1)) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1,
        g (ω : EuclideanSpace ℝ (Fin (m + 1))) ∂(sphereMeasure (m + 1))
      = ∫⁻ t in Ioo (-1 : ℝ) 1, ENNReal.ofReal (sliceDensity m t) *
          ∫⁻ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
            g (heightPoint m t (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m) := by
  haveI := nontrivial_euclidean (show 1 ≤ m + 1 by omega)
  set F : EuclideanSpace ℝ (Fin (m + 1)) → ℝ≥0∞ :=
    fun x => g (‖x‖⁻¹ • x) * radialBump ‖x‖ with hFdef
  have hFmeas : Measurable F :=
    (hg.comp ((measurable_norm.inv).smul measurable_id)).mul
      (measurable_radialBump.comp measurable_norm)
  -- the value of `F` on a scaled unit vector
  have hFval : ∀ (r : ℝ), 0 < r → ∀ x : EuclideanSpace ℝ (Fin (m + 1)), ‖x‖ = 1 →
      F (r • x) = g x * radialBump r := by
    intro r hr x hx
    have hnorm : ‖r • x‖ = r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hx, mul_one]
    rw [hFdef]
    simp only []
    rw [hnorm, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  set C : ℝ≥0∞ := ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ m) * radialBump r with hCdef
  have hC0 : C ≠ 0 := by
    have := radialBump_integral_pos m
    rw [← hCdef] at this
    exact fun h => by simp [h] at this
  have hCtop : C ≠ ⊤ := by
    have := radialBump_integral_lt_top m
    rwa [← hCdef] at this
  -- first evaluation, by polar coordinates
  have hA : ∫⁻ x, F x ∂(volume : Measure (EuclideanSpace ℝ (Fin (m + 1))))
      = C * ∫⁻ ω : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1,
          g (ω : EuclideanSpace ℝ (Fin (m + 1))) ∂(sphereMeasure (m + 1)) := by
    have h := lintegral_polar (volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))) F hFmeas
    rw [finrank_eq] at h
    simp only [Nat.add_sub_cancel] at h
    rw [h]
    have hinner : EqOn (fun r : ℝ => ENNReal.ofReal (r ^ m) *
          ∫⁻ ω : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1,
            F (r • (ω : EuclideanSpace ℝ (Fin (m + 1)))) ∂(sphereMeasure (m + 1)))
        (fun r : ℝ => (ENNReal.ofReal (r ^ m) * radialBump r) *
          ∫⁻ ω : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1,
            g (ω : EuclideanSpace ℝ (Fin (m + 1))) ∂(sphereMeasure (m + 1))) (Ioi (0 : ℝ)) := by
      intro r hr
      have hr0 : (0 : ℝ) < r := hr
      have : ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1,
          F (r • (ω : EuclideanSpace ℝ (Fin (m + 1)))) =
            g (ω : EuclideanSpace ℝ (Fin (m + 1))) * radialBump r := fun ω =>
        hFval r hr0 _ (mem_sphere_zero_iff_norm.1 ω.2)
      simp only [this]
      rw [lintegral_mul_const' _ _ (radialBump_ne_top r)]
      ring
    rw [setLIntegral_congr_fun measurableSet_Ioi hinner,
      lintegral_mul_const _ (measurable_radialWeight m), hCdef]
  -- second evaluation, by the height parametrisation
  have hB : ∫⁻ x, F x ∂(volume : Measure (EuclideanSpace ℝ (Fin (m + 1))))
      = C * ∫⁻ t in Ioo (-1 : ℝ) 1, ENNReal.ofReal (sliceDensity m t) *
          ∫⁻ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
            g (heightPoint m t (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m) := by
    rw [lintegral_height_polar m hm hFmeas]
    have hinner : EqOn (fun r : ℝ => ENNReal.ofReal (r ^ m) *
          ∫⁻ u in Ioo (-1 : ℝ) 1, ENNReal.ofReal (sliceDensity m u) *
            ∫⁻ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
              F (r • heightPoint m u (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m))
        (fun r : ℝ => (ENNReal.ofReal (r ^ m) * radialBump r) *
          ∫⁻ u in Ioo (-1 : ℝ) 1, ENNReal.ofReal (sliceDensity m u) *
            ∫⁻ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
              g (heightPoint m u (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m))
        (Ioi (0 : ℝ)) := by
      intro r hr
      have hr0 : (0 : ℝ) < r := hr
      have hu : EqOn (fun u : ℝ => ENNReal.ofReal (sliceDensity m u) *
            ∫⁻ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
              F (r • heightPoint m u (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m))
          (fun u : ℝ => (ENNReal.ofReal (sliceDensity m u) *
            ∫⁻ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
              g (heightPoint m u (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m))
            * radialBump r) (Ioo (-1 : ℝ) 1) := by
        intro u hu
        have hval : ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
            F (r • heightPoint m u (ω : EuclideanSpace ℝ (Fin m)))
              = g (heightPoint m u (ω : EuclideanSpace ℝ (Fin m))) * radialBump r := by
          intro ω
          exact hFval r hr0 _
            (norm_heightPoint ⟨hu.1.le, hu.2.le⟩ (mem_sphere_zero_iff_norm.1 ω.2))
        simp only [hval]
        rw [lintegral_mul_const' _ _ (radialBump_ne_top r)]
        ring
      show ENNReal.ofReal (r ^ m) *
          ∫⁻ u in Ioo (-1 : ℝ) 1, ENNReal.ofReal (sliceDensity m u) *
            ∫⁻ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
              F (r • heightPoint m u (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m)
        = ENNReal.ofReal (r ^ m) * radialBump r *
          ∫⁻ u in Ioo (-1 : ℝ) 1, ENNReal.ofReal (sliceDensity m u) *
            ∫⁻ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
              g (heightPoint m u (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m)
      rw [setLIntegral_congr_fun measurableSet_Ioo hu,
        lintegral_mul_const' _ _ (radialBump_ne_top r)]
      ring
    rw [setLIntegral_congr_fun measurableSet_Ioi hinner,
      lintegral_mul_const _ (measurable_radialWeight m), hCdef]
  exact (ENNReal.mul_right_inj hC0 hCtop).1 (hA.symm.trans hB)


/-! ## The slicing identity as an identity of measures -/

/-- The height parameter clamped to `[-1,1]` (used only to give the parametrisation a total
definition; the measure used below is carried by `(-1,1)`). -/
def clampHeight (t : ℝ) : ℝ := max (-1) (min 1 t)

theorem clampHeight_mem (t : ℝ) : clampHeight t ∈ Icc (-1 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem clampHeight_eq_self {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) : clampHeight t = t := by
  rw [clampHeight, min_eq_right ht.2.le, max_eq_right ht.1.le]

theorem measurable_clampHeight : Measurable clampHeight :=
  measurable_const.max (measurable_const.min measurable_id)

/-- The height parametrisation `(t, ω) ↦ (t, √(1-t²) ω)` of the unit sphere of `ℝ^{m+1}`. -/
def heightSplit (m : ℕ) (p : ℝ × sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
    sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 :=
  ⟨heightPoint m (clampHeight p.1) (p.2 : EuclideanSpace ℝ (Fin m)),
    mem_sphere_zero_iff_norm.2
      (norm_heightPoint (clampHeight_mem p.1) (mem_sphere_zero_iff_norm.1 p.2.2))⟩

theorem heightSplit_coe (m : ℕ) (p : ℝ × sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
    (heightSplit m p : EuclideanSpace ℝ (Fin (m + 1)))
      = heightPoint m (clampHeight p.1) (p.2 : EuclideanSpace ℝ (Fin m)) := rfl

theorem measurable_heightSplit (m : ℕ) : Measurable (heightSplit m) :=
  Measurable.subtype_mk ((measurable_heightPoint m).comp
    (Measurable.prodMk (measurable_clampHeight.comp measurable_fst)
      (measurable_subtype_coe.comp measurable_snd)))

/-- The height measure `(1-t²)^{(m-2)/2} dt` on `(-1,1)`. -/
def heightMeasure (m : ℕ) : Measure ℝ :=
  (volume.restrict (Ioo (-1 : ℝ) 1)).withDensity
    (fun t => ENNReal.ofReal (sliceDensity m t))

instance instSFiniteHeightMeasure (m : ℕ) : SFinite (heightMeasure m) := by
  unfold heightMeasure
  infer_instance

theorem lintegral_heightMeasure (m : ℕ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ t, f t ∂(heightMeasure m)
      = ∫⁻ t in Ioo (-1 : ℝ) 1, ENNReal.ofReal (sliceDensity m t) * f t := by
  rw [heightMeasure, lintegral_withDensity_eq_lintegral_mul _
    (measurable_ofReal_sliceDensity m) hf]
  simp only [Pi.mul_apply]

/-- **The slicing identity, as an identity of measures.**  Mathlib's sphere measure on
`S^m ⊂ ℝ^{m+1}` is the push-forward of `(1-t²)^{(m-2)/2} dt ⊗ σ_{m-1}` under the height
parametrisation. -/
theorem map_heightSplit (m : ℕ) (hm : 1 ≤ m) :
    Measure.map (heightSplit m) ((heightMeasure m).prod (sphereMeasure m))
      = sphereMeasure (m + 1) := by
  refine (Measure.ext fun s hs => ?_)
  have hsph : MeasurableSet (sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :=
    Metric.isClosed_sphere.measurableSet
  have himg : MeasurableSet ((Subtype.val : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 → _) '' s)
      := (MeasurableEmbedding.subtype_coe hsph).measurableSet_image' hs
  set g : EuclideanSpace ℝ (Fin (m + 1)) → ℝ≥0∞ :=
    Set.indicator ((Subtype.val : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 → _) '' s) 1
    with hgdef
  have hgmeas : Measurable g := measurable_one.indicator himg
  have hmemiff : ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1,
      ((ω : EuclideanSpace ℝ (Fin (m + 1))) ∈
        (Subtype.val : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 → _) '' s) ↔ ω ∈ s := by
    intro ω
    constructor
    · rintro ⟨y, hy, hxy⟩
      have : y = ω := Subtype.val_injective hxy
      exact this ▸ hy
    · intro hω; exact Set.mem_image_of_mem _ hω
  have hkey := lintegral_sphere_slicing m hm hgmeas
  -- the left-hand side is the measure of `s`
  have hL : ∫⁻ ω : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1,
      g (ω : EuclideanSpace ℝ (Fin (m + 1))) ∂(sphereMeasure (m + 1))
      = sphereMeasure (m + 1) s := by
    have hfun : (fun ω : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 =>
        g (ω : EuclideanSpace ℝ (Fin (m + 1)))) = Set.indicator s 1 := by
      funext ω
      by_cases hω : ω ∈ s
      · rw [hgdef, Set.indicator_of_mem ((hmemiff ω).2 hω), Set.indicator_of_mem hω]
        rfl
      · rw [hgdef, Set.indicator_of_notMem (fun h => hω ((hmemiff ω).1 h)),
          Set.indicator_of_notMem hω]
    rw [hfun, lintegral_indicator_one hs]
  -- the right-hand side is the push-forward measure of `s`
  set P : Set (ℝ × sphere (0 : EuclideanSpace ℝ (Fin m)) 1) := heightSplit m ⁻¹' s with hPdef
  have hP : MeasurableSet P := (measurable_heightSplit m) hs
  have hR : ∫⁻ t in Ioo (-1 : ℝ) 1, ENNReal.ofReal (sliceDensity m t) *
      ∫⁻ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        g (heightPoint m t (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m)
      = Measure.map (heightSplit m) ((heightMeasure m).prod (sphereMeasure m)) s := by
    rw [Measure.map_apply (measurable_heightSplit m) hs, ← hPdef,
      ← lintegral_indicator_one hP,
      lintegral_prod _ (measurable_one.indicator hP).aemeasurable,
      lintegral_heightMeasure m
        ((measurable_one.indicator hP).lintegral_prod_right' (ν := sphereMeasure m))]
    refine setLIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
    congr 1
    refine lintegral_congr fun ω => ?_
    have hcoe : heightPoint m t (ω : EuclideanSpace ℝ (Fin m))
        = ((heightSplit m (t, ω) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
            EuclideanSpace ℝ (Fin (m + 1))) := by
      rw [heightSplit_coe, clampHeight_eq_self ht]
    rw [hcoe]
    by_cases hmem : (t, ω) ∈ P
    · rw [Set.indicator_of_mem hmem, hgdef, Set.indicator_of_mem ((hmemiff _).2 hmem)]
      rfl
    · rw [Set.indicator_of_notMem hmem, hgdef,
        Set.indicator_of_notMem (fun h => hmem ((hmemiff _).1 h))]
  rw [← hR, ← hkey, hL]


/-! ## The Bochner form of the slicing formula -/

/-- **The slicing formula for mathlib's sphere measure** (Bochner form). -/
theorem integral_sphere_slicing (m : ℕ) (hm : 1 ≤ m)
    {f : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 → ℝ}
    (hf : Integrable f (sphereMeasure (m + 1))) :
    ∫ ω, f ω ∂(sphereMeasure (m + 1))
      = ∫ t in Ioo (-1 : ℝ) 1, sliceDensity m t *
          ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
            f (heightSplit m (t, ω)) ∂(sphereMeasure m) := by
  have hmap := map_heightSplit m hm
  have hφ : AEMeasurable (heightSplit m) ((heightMeasure m).prod (sphereMeasure m)) :=
    (measurable_heightSplit m).aemeasurable
  have hfsm : AEStronglyMeasurable f
      (Measure.map (heightSplit m) ((heightMeasure m).prod (sphereMeasure m))) := by
    rw [hmap]; exact hf.aestronglyMeasurable
  have hint : Integrable (fun p => f (heightSplit m p))
      ((heightMeasure m).prod (sphereMeasure m)) :=
    (integrable_map_measure hfsm hφ).1 (by rw [hmap]; exact hf)
  calc ∫ ω, f ω ∂(sphereMeasure (m + 1))
      = ∫ ω, f ω ∂(Measure.map (heightSplit m)
          ((heightMeasure m).prod (sphereMeasure m))) := by rw [hmap]
    _ = ∫ p, f (heightSplit m p) ∂((heightMeasure m).prod (sphereMeasure m)) :=
        integral_map hφ hfsm
    _ = ∫ t, (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
          f (heightSplit m (t, ω)) ∂(sphereMeasure m)) ∂(heightMeasure m) :=
        integral_prod _ hint
    _ = _ := by
        rw [heightMeasure]
        simp only [ENNReal.ofReal]
        rw [integral_withDensity_eq_integral_smul (measurable_sliceDensity m).real_toNNReal]
        refine setIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
        rw [NNReal.smul_def, Real.coe_toNNReal _ (sliceDensity_nonneg m ht), smul_eq_mul]

/-! ## Sanity check: the total mass -/

/-- **The total mass check.**  Slicing with `f = 1` recovers `sphere_measure_univ`:
`(∫_{-1}^1 (1-t²)^{(m-2)/2} dt) · m ω_m = (m+1) ω_{m+1}`. -/
theorem sphereSlice_total_mass (m : ℕ) (hm : 1 ≤ m) :
    (∫ t in Ioo (-1 : ℝ) 1, sliceDensity m t) * ((m : ℝ) * omega m)
      = ((m : ℝ) + 1) * omega (m + 1) := by
  have h := integral_sphere_slicing m hm
    (f := fun _ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 => (1 : ℝ))
    (integrable_const 1)
  rw [integral_const, smul_eq_mul, mul_one, measureReal_def,
    sphere_measure_univ (m + 1) (by omega)] at h
  have hinner : ∀ t : ℝ, sliceDensity m t *
      ∫ _ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1, (1 : ℝ) ∂(sphereMeasure m)
      = sliceDensity m t * ((m : ℝ) * omega m) := by
    intro t
    rw [integral_const, smul_eq_mul, mul_one, measureReal_def, sphere_measure_univ m hm]
  simp only [hinner] at h
  rw [integral_mul_const] at h
  rw [← h]
  push_cast
  ring

/-! ## The hemispherical end cap -/

/-- The area element of the hemispherical cap is the slicing density, shifted by one. -/
theorem capAreaElement_hemisphere (m : ℕ) (hm : 1 ≤ m) {s : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 0) :
    capAreaElement (Cap.hemisphere m) s = sliceDensity m (s + 1) := by
  have hpos : 0 < 1 - (s + 1) ^ 2 := by nlinarith [hs.1, hs.2]
  have hsemi_pos : 0 < Cap.semi 1 s := Cap.semi_pos 1 (le_refl 1) ⟨hs.1, hs.2⟩
  have hderiv : deriv (Cap.semi 1) s = Cap.semiD 1 s := Cap.deriv_semi 1 hpos
  have hsqrt : Real.sqrt (1 + (deriv (Cap.semi 1) s) ^ 2) = 1 / Cap.semi 1 s := by
    rw [hderiv]
    have hmain : 1 + (Cap.semiD 1 s) ^ 2 = (1 / Cap.semi 1 s) ^ 2 := by
      simp only [Cap.semiD, Cap.semi]
      field_simp
      rw [Real.sq_sqrt hpos.le]
      ring
    rw [hmain, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  have h2 : (Cap.semi 1 s) ^ 2 = 1 - (s + 1) ^ 2 := Real.sq_sqrt hpos.le
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    have := Nat.cast_sub (R := ℝ) hm
    simpa using this
  simp only [capAreaElement, Cap.hemisphere]
  rw [hsqrt, sliceDensity, ← h2]
  have h3 : ((Cap.semi 1 s) ^ 2) ^ (((m : ℝ) - 2) / 2) = (Cap.semi 1 s) ^ ((m : ℝ) - 2) := by
    rw [← Real.rpow_natCast (Cap.semi 1 s) 2, ← Real.rpow_mul hsemi_pos.le]
    congr 1
    push_cast
    ring
  rw [h3, ← Real.rpow_natCast (Cap.semi 1 s) (m - 1), hcast,
    show (m : ℝ) - 2 = ((m : ℝ) - 1) + (-(1 : ℝ)) by ring, Real.rpow_add hsemi_pos,
    Real.rpow_neg hsemi_pos.le 1, Real.rpow_one]
  ring

/-- The integrand on `S^m` matching the lateral boundary of the hemispherical end cap:
`ω ↦ G(ω₀ - 1, ω')` on the open upper half-sphere, `0` elsewhere. -/
def capSphereFun (m : ℕ) (G : CapSpace m → ℝ)
    (ω : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) : ℝ :=
  if 0 < (ω : EuclideanSpace ℝ (Fin (m + 1))) 0 then
    G ((ω : EuclideanSpace ℝ (Fin (m + 1))) 0 - 1,
      (ofEuclid m (ω : EuclideanSpace ℝ (Fin (m + 1)))).2)
  else 0

theorem capSphereFun_heightSplit (m : ℕ) (G : CapSpace m → ℝ) {t : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 1) (ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
    capSphereFun m G (heightSplit m (t, ω))
      = if 0 < t then
          G (t - 1, Real.sqrt (1 - t ^ 2) • (ω : EuclideanSpace ℝ (Fin m))) else 0 := by
  have hc : (heightSplit m (t, ω) : EuclideanSpace ℝ (Fin (m + 1)))
      = toEuclid m (t, Real.sqrt (1 - t ^ 2) • (ω : EuclideanSpace ℝ (Fin m))) := by
    rw [heightSplit_coe, clampHeight_eq_self ht, heightPoint]
  simp only [capSphereFun, hc, toEuclid_apply_zero, ofEuclid_toEuclid]

/-- **Identification of the two parametrisations of the hemispherical lateral boundary.**
The lateral boundary integral of the unit hemispherical end cap (in the surface-of-revolution
coordinates of `RobinCaps.ThinDomain.capLateralIntegral`) is the integral, against mathlib's
sphere measure of `S^m ⊂ ℝ^{m+1}`, of the shifted integrand over the open upper half-sphere. -/
theorem capLateralIntegral_hemisphere_eq (m : ℕ) (hm : 1 ≤ m) (G : CapSpace m → ℝ)
    (hG : Integrable (capSphereFun m G) (sphereMeasure (m + 1))) :
    capLateralIntegral (Cap.hemisphere m) G
      = ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1,
          capSphereFun m G ω ∂(sphereMeasure (m + 1)) := by
  set Φ : ℝ → ℝ := fun t => sliceDensity m t *
    ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      G (t - 1, Real.sqrt (1 - t ^ 2) • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m)
    with hΦdef
  have hRHS : ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1,
      capSphereFun m G ω ∂(sphereMeasure (m + 1)) = ∫ t in Ioo (0 : ℝ) 1, Φ t := by
    rw [integral_sphere_slicing m hm hG,
      ← integral_indicator (measurableSet_Ioo (a := (-1 : ℝ)) (b := 1)),
      ← integral_indicator (measurableSet_Ioo (a := (0 : ℝ)) (b := 1))]
    congr 1
    funext t
    by_cases ht1 : t ∈ Ioo (0 : ℝ) 1
    · have ht : t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [ht1.1], ht1.2⟩
      rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht1, hΦdef]
      simp only []
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      show capSphereFun m G (heightSplit m (t, ω))
        = G (t - 1, Real.sqrt (1 - t ^ 2) • (ω : EuclideanSpace ℝ (Fin m)))
      rw [capSphereFun_heightSplit m G ht ω, if_pos ht1.1]
    · rw [Set.indicator_of_notMem ht1]
      by_cases ht : t ∈ Ioo (-1 : ℝ) 1
      · rw [Set.indicator_of_mem ht]
        have htle : ¬ (0 : ℝ) < t := fun h => ht1 ⟨h, ht.2⟩
        have : ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
            capSphereFun m G (heightSplit m (t, ω)) = 0 := by
          intro ω
          rw [capSphereFun_heightSplit m G ht ω, if_neg htle]
        simp only [this, integral_zero, mul_zero]
      · rw [Set.indicator_of_notMem ht]
  rw [hRHS, capLateralIntegral]
  have hK : (-(Cap.hemisphere m).K : ℝ) = -1 := rfl
  rw [hK]
  have hstep : ∀ s ∈ Ioo (-1 : ℝ) 0, capLateralDensity (Cap.hemisphere m) G s = Φ (s + 1) := by
    intro s hs
    rw [capLateralDensity, capAreaElement_hemisphere m hm hs, hΦdef]
    simp only [add_sub_cancel_right]
    rfl
  rw [setIntegral_congr_fun measurableSet_Ioo hstep,
    ← intervalIntegral_eq_integral_Ioo (by norm_num : (-1 : ℝ) ≤ 0),
    intervalIntegral.integral_comp_add_right Φ 1]
  norm_num
  rw [intervalIntegral_eq_integral_Ioo (by norm_num : (0 : ℝ) ≤ 1)]

end RobinCaps.ThinDomain

end
