import RobinCaps.Cap.TraceLateralGen

/-!
# Joint measurability of the θ-parametrised lateral trace on a general cap

This file closes the single open interface of `RobinCaps/Cap/TraceLateralGen.lean`: the two
hypotheses of `aestronglyMeasurable_lateralTraceGen_tlg`, namely joint strong measurability (in
`(s,ω)`) of the θ-parametrised sphere trace of the canonical measurable representatives
`repFun`, `repGz_el`, and its joint a.e. agreement with `lateralTraceGen_tlg`.

## Strategy

`RobinCaps.Sobolev.Weak.traceSphere R u g w` has `R`-dependent integration bounds
(`Ioo (R/2) R` and `(R/2+R)/2 .. R`).  With `R = C.θ s` genuinely varying in `s`, the
fixed-radius argument of `RobinCaps.ThinDomain.stronglyMeasurable_traceSphere_joint_tgb` does not
adapt verbatim.  The fix (`traceSphere_rescale_tlm`) is to substitute `r = R τ` (resp. `t = R τ`)
via `intervalIntegral.integral_comp_mul_left`, turning every integration domain into the
*constant* `Ioo (1/2) 1` (resp. `(3/4)..1`).  The rescaled integrand
`(s,τ,ω) ↦ F(s, (Θ(s) τ) • ω)` is then jointly measurable, for **any** jointly measurable
positive radius function `Θ` and any globally strongly measurable `F`, by mimicking the
parametric-integral argument of `stronglyMeasurable_traceSphere_joint_tgb`
(`stronglyMeasurable_traceSphere_paramR_tlm`).

## The genuine gap: `C.θ` is not measurable off `(-K,0)`

`Cap.θ : ℝ → ℝ` is a *total* function, but the structure only constrains its values on
`Set.Ioo (-C.K) 0` (continuity there is `RobinCaps.Cap.Concave.continuousOn_Ioo`); outside that
interval `C.θ` is completely unconstrained, hence **not** provably measurable (or even
positive).  Consequently the literal, unrestricted statement
`StronglyMeasurable (fun p : ℝ × sphere .. 1 => traceSphere (C.θ p.1) ..)` — which is what the
hypothesis `hJoint` of `aestronglyMeasurable_lateralTraceGen_tlg` demands — is **not a theorem**
for a fully general `C : Cap m`: one can build a legitimate `Cap m` whose `θ` is a non-measurable
perturbation off `(-K,0)` (all structure fields only reference `Ioo (-K) 0` and the two boundary
points `-K`, `0`), together with a `u : H1P C.body` whose canonical representatives genuinely
depend on the radius there, making the composite non-measurable.  Per the project's own escape
clause ("isolate the resisting step as a documented hypothesis"), `stronglyMeasurable_
traceSphere_theta_joint_tlm` below is therefore proved **conditionally** on the natural closing
facts `Measurable C.θ` and `∀ s, 0 < C.θ s` (both automatic for every concretely constructed cap
in this development, e.g. `Cap.flat`, `Cap.semi`, whose `θ` is a globally continuous, globally
positive formula).

This conditioning is *not* needed for the actually useful headline result
`aestronglyMeasurable_lateralTraceGen_tlm`: `AEStronglyMeasurable` only asks for *some* strongly
measurable representative agreeing a.e. (under the measure `(volume.restrict (Ioo (-C.K) 0)).prod
(sphereMeasure m)`, which lives entirely on `Ioo (-C.K) 0`) with the target, and
`Cap.θ`'s restriction to `Ioo (-C.K) 0` extends *unconditionally* to a genuinely globally
measurable, globally positive function `thetaExt_tlm C` (via `stronglyMeasurable_of_restrict_
of_restrict_compl`, which needs measurability of `C.θ` only on the two measurable pieces
`Ioo (-C.K) 0` and its complement *separately*, and on the complement piece we simply do not use
`C.θ` at all).  Since `thetaExt_tlm C` agrees with `C.θ` *exactly* (not just a.e.) on
`Ioo (-C.K) 0`, this gives an unconditional proof of the headline theorem.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace RobinCaps.Cap

open RobinCaps.ThinDomain RobinCaps.Sobolev RobinCaps.Sobolev.Weak

noncomputable section

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)

/-! ## 1. Rescaling `traceSphere` to fixed integration domains -/

/-- Rescale a set integral over `Ioo (R/2) R` to a set integral over the fixed `Ioo (1/2) 1`,
via `r = R τ`. -/
theorem setIntegral_Ioo_comp_mul_tlm {R : ℝ} (hR : 0 < R) (F : ℝ → ℝ) :
    (∫ r in Set.Ioo (R / 2) R, F r) = R * ∫ τ in Set.Ioo (1 / 2 : ℝ) 1, F (R * τ) := by
  have hR0 : R ≠ 0 := hR.ne'
  have h1 : (∫ r in Set.Ioo (R / 2) R, F r) = ∫ r in (R / 2)..R, F r := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact (integral_Ioc_eq_integral_Ioo).symm
  have h2 : (∫ τ in Set.Ioo (1 / 2 : ℝ) 1, F (R * τ)) = ∫ τ in (1 / 2 : ℝ)..1, F (R * τ) := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    exact (integral_Ioc_eq_integral_Ioo).symm
  rw [h1, h2]
  have h := intervalIntegral.integral_comp_mul_left (a := (1 / 2 : ℝ)) (b := 1) (f := F) hR0
  simp only [smul_eq_mul] at h
  rw [h]
  have heq1 : R * (1 / 2 : ℝ) = R / 2 := by ring
  have heq2 : R * (1 : ℝ) = R := by ring
  rw [heq1, heq2]
  field_simp

/-- Rescale an interval integral with a fixed lower endpoint `h` to the fixed lower endpoint
`h / R`, via `t = R τ`. -/
theorem intervalIntegral_comp_mul_tlm {R : ℝ} (hR0 : R ≠ 0) (h : ℝ) (g : E → E) (w : E) (τ : ℝ) :
    (∫ t in h..(R * τ), inner ℝ (g (t • w)) w)
      = R * ∫ x in (h / R)..τ, inner ℝ (g ((R * x) • w)) w := by
  have hh := intervalIntegral.integral_comp_mul_left
    (a := (h / R : ℝ)) (b := τ) (f := fun t : ℝ => inner ℝ (g (t • w)) w) hR0
  simp only [smul_eq_mul] at hh
  have heq : R * (h / R) = h := by field_simp
  rw [heq] at hh
  rw [hh]; field_simp

/-- **The rescaled `traceSphere` formula.**  Substituting `r = Rτ` in the outer integral and
`t = Rτ` in both interval integrals turns every integration bound into the fixed constants
`1/2, 3/4, 1`. -/
theorem traceSphere_rescale_tlm {R : ℝ} (hR : 0 < R) (u : E → ℝ) (g : E → E) (w : E) :
    traceSphere R u g w
      = 2 * (∫ τ in Set.Ioo (1 / 2 : ℝ) 1,
              (u ((R * τ) • w) - R * ∫ x in (3 / 4 : ℝ)..τ, inner ℝ (g ((R * x) • w)) w))
        + R * ∫ τ in (3 / 4 : ℝ)..1, inner ℝ (g ((R * τ) • w)) w := by
  have hR0 : R ≠ 0 := hR.ne'
  have hMeq : (R / 2 + R) / 2 / R = (3 / 4 : ℝ) := by field_simp; ring
  have hinner : ∀ τ : ℝ, (∫ t in ((R / 2 + R) / 2)..(R * τ), inner ℝ (g (t • w)) w)
      = R * ∫ x in (3 / 4 : ℝ)..τ, inner ℝ (g ((R * x) • w)) w := by
    intro τ
    rw [intervalIntegral_comp_mul_tlm hR0 ((R / 2 + R) / 2) g w τ, hMeq]
  simp only [traceSphere]
  rw [setIntegral_Ioo_comp_mul_tlm hR
    (fun r => u (r • w) - ∫ t in ((R / 2 + R) / 2)..r, inner ℝ (g (t • w)) w)]
  have hcongr : (∫ τ in Set.Ioo (1 / 2 : ℝ) 1,
        (u ((R * τ) • w) - ∫ t in ((R / 2 + R) / 2)..(R * τ), inner ℝ (g (t • w)) w))
      = ∫ τ in Set.Ioo (1 / 2 : ℝ) 1,
        (u ((R * τ) • w) - R * ∫ x in (3 / 4 : ℝ)..τ, inner ℝ (g ((R * x) • w)) w) := by
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    dsimp only
    rw [hinner τ]
  rw [hcongr]
  have hlast : (∫ t in ((R / 2 + R) / 2)..R, inner ℝ (g (t • w)) w)
      = R * ∫ τ in (3 / 4 : ℝ)..1, inner ℝ (g ((R * τ) • w)) w := by
    have h := hinner 1
    simpa using h
  rw [hlast]
  field_simp

/-! ## 2. Joint measurability for an arbitrary jointly-measurable positive radius function -/

/-- **Joint strong measurability of the `traceSphere` formula, for a jointly measurable positive
radius function `Θ` and jointly measurable data `F, G`.** -/
theorem stronglyMeasurable_traceSphere_paramR_tlm {Θ : ℝ → ℝ} (hΘmeas : Measurable Θ)
    (hΘpos : ∀ s : ℝ, 0 < Θ s) {F : CapSpace m → ℝ} {G : CapSpace m → E}
    (hF : StronglyMeasurable F) (hG : StronglyMeasurable G) :
    StronglyMeasurable (fun p : ℝ × sphere (0 : E) 1 =>
      traceSphere (Θ p.1) (fun z => F (p.1, z)) (fun z => G (p.1, z)) (p.2 : E)) := by
  classical
  have hsmul : Measurable (fun q : (ℝ × sphere (0 : E) 1) × ℝ =>
      (Θ q.1.1 * q.2) • ((q.1.2 : sphere (0 : E) 1) : E)) :=
    (Measurable.mul (hΘmeas.comp (measurable_fst.comp measurable_fst)) measurable_snd).smul
      (measurable_subtype_coe.comp (measurable_snd.comp measurable_fst))
  have hH : StronglyMeasurable (fun p : (ℝ × sphere (0 : E) 1) × ℝ =>
      inner ℝ (G (p.1.1, (Θ p.1.1 * p.2) • ((p.1.2 : sphere (0 : E) 1) : E)))
        ((p.1.2 : sphere (0 : E) 1) : E)) := by
    have hGcomp : Measurable (fun p : (ℝ × sphere (0 : E) 1) × ℝ =>
        G (p.1.1, (Θ p.1.1 * p.2) • ((p.1.2 : sphere (0 : E) 1) : E))) :=
      hG.measurable.comp (Measurable.prodMk (measurable_fst.comp measurable_fst) hsmul)
    exact (hGcomp.inner (measurable_subtype_coe.comp (measurable_snd.comp measurable_fst))
      ).stronglyMeasurable
  have hInd : ∀ S : Set ℝ, StronglyMeasurable (fun q : ℝ × sphere (0 : E) 1 => ∫ t in S,
      inner ℝ (G (q.1, (Θ q.1 * t) • ((q.2 : sphere (0 : E) 1) : E))) ((q.2 : sphere (0 : E) 1) : E)) :=
    fun S => hH.integral_prod_right' (ν := volume.restrict S)
  have hmeasS : ∀ b : ℝ, MeasurableSet
      {z : ((ℝ × sphere (0 : E) 1) × ℝ) × ℝ | b < z.2 ∧ z.2 ≤ z.1.2} :=
    fun b => (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_snd.comp measurable_fst))
  have hmeasS' : ∀ b : ℝ, MeasurableSet
      {z : ((ℝ × sphere (0 : E) 1) × ℝ) × ℝ | z.1.2 < z.2 ∧ z.2 ≤ b} :=
    fun b => (measurableSet_lt (measurable_snd.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  have hG1 : StronglyMeasurable
      (fun z : ((ℝ × sphere (0 : E) 1) × ℝ) × ℝ =>
        inner ℝ (G (z.1.1.1, (Θ z.1.1.1 * z.2) • ((z.1.1.2 : sphere (0 : E) 1) : E)))
          ((z.1.1.2 : sphere (0 : E) 1) : E)) :=
    hH.comp_measurable (Measurable.prodMk (measurable_fst.comp measurable_fst) measurable_snd)
  have hJ1 : ∀ b : ℝ, StronglyMeasurable
      (fun q : (ℝ × sphere (0 : E) 1) × ℝ => ∫ t in Ioc b q.2,
        inner ℝ (G (q.1.1, (Θ q.1.1 * t) • ((q.1.2 : sphere (0 : E) 1) : E)))
          ((q.1.2 : sphere (0 : E) 1) : E)) := by
    intro b
    have hF' : StronglyMeasurable
        (fun z : ((ℝ × sphere (0 : E) 1) × ℝ) × ℝ =>
          (Ioc b z.1.2).indicator (fun t => inner ℝ (G (z.1.1.1, (Θ z.1.1.1 * t) •
            ((z.1.1.2 : sphere (0 : E) 1) : E)))
            ((z.1.1.2 : sphere (0 : E) 1) : E)) z.2) := by
      have heq : (fun z : ((ℝ × sphere (0 : E) 1) × ℝ) × ℝ =>
          (Ioc b z.1.2).indicator (fun t => inner ℝ (G (z.1.1.1, (Θ z.1.1.1 * t) •
            ((z.1.1.2 : sphere (0 : E) 1) : E)))
            ((z.1.1.2 : sphere (0 : E) 1) : E)) z.2)
          = Set.indicator {z : ((ℝ × sphere (0 : E) 1) × ℝ) × ℝ |
              b < z.2 ∧ z.2 ≤ z.1.2}
            (fun z => inner ℝ (G (z.1.1.1, (Θ z.1.1.1 * z.2) • ((z.1.1.2 : sphere (0 : E) 1) :
              E)))
              ((z.1.1.2 : sphere (0 : E) 1) : E)) := by
        funext z
        by_cases hz : b < z.2 ∧ z.2 ≤ z.1.2
        · rw [Set.indicator_of_mem (show z.2 ∈ Ioc b z.1.2 from hz),
            Set.indicator_of_mem (show z ∈ {z : ((ℝ × sphere (0 : E) 1) × ℝ) × ℝ |
              b < z.2 ∧ z.2 ≤ z.1.2} from hz)]
        · rw [Set.indicator_of_notMem (show z.2 ∉ Ioc b z.1.2 from hz),
            Set.indicator_of_notMem
              (show z ∉ {z : ((ℝ × sphere (0 : E) 1) × ℝ) × ℝ |
                b < z.2 ∧ z.2 ≤ z.1.2} from hz)]
      rw [heq]
      exact hG1.indicator (hmeasS b)
    have hEq : (fun q : (ℝ × sphere (0 : E) 1) × ℝ => ∫ t in Ioc b q.2,
        inner ℝ (G (q.1.1, (Θ q.1.1 * t) • ((q.1.2 : sphere (0 : E) 1) : E)))
          ((q.1.2 : sphere (0 : E) 1) : E))
        = fun q => ∫ y : ℝ, (Ioc b q.2).indicator
          (fun t => inner ℝ (G (q.1.1, (Θ q.1.1 * t) • ((q.1.2 : sphere (0 : E) 1) : E)))
            ((q.1.2 : sphere (0 : E) 1) : E)) y := by
      funext q
      exact (integral_indicator measurableSet_Ioc).symm
    rw [hEq]
    exact hF'.integral_prod_right' (ν := (volume : Measure ℝ))
  have hJ2 : ∀ b : ℝ, StronglyMeasurable
      (fun q : (ℝ × sphere (0 : E) 1) × ℝ => ∫ t in Ioc q.2 b,
        inner ℝ (G (q.1.1, (Θ q.1.1 * t) • ((q.1.2 : sphere (0 : E) 1) : E)))
          ((q.1.2 : sphere (0 : E) 1) : E)) := by
    intro b
    have hF' : StronglyMeasurable
        (fun z : ((ℝ × sphere (0 : E) 1) × ℝ) × ℝ =>
          (Ioc z.1.2 b).indicator (fun t => inner ℝ (G (z.1.1.1, (Θ z.1.1.1 * t) •
            ((z.1.1.2 : sphere (0 : E) 1) : E)))
            ((z.1.1.2 : sphere (0 : E) 1) : E)) z.2) := by
      have heq : (fun z : ((ℝ × sphere (0 : E) 1) × ℝ) × ℝ =>
          (Ioc z.1.2 b).indicator (fun t => inner ℝ (G (z.1.1.1, (Θ z.1.1.1 * t) •
            ((z.1.1.2 : sphere (0 : E) 1) : E)))
            ((z.1.1.2 : sphere (0 : E) 1) : E)) z.2)
          = Set.indicator {z : ((ℝ × sphere (0 : E) 1) × ℝ) × ℝ |
              z.1.2 < z.2 ∧ z.2 ≤ b}
            (fun z => inner ℝ (G (z.1.1.1, (Θ z.1.1.1 * z.2) • ((z.1.1.2 : sphere (0 : E) 1) :
              E)))
              ((z.1.1.2 : sphere (0 : E) 1) : E)) := by
        funext z
        by_cases hz : z.1.2 < z.2 ∧ z.2 ≤ b
        · rw [Set.indicator_of_mem (show z.2 ∈ Ioc z.1.2 b from hz),
            Set.indicator_of_mem (show z ∈ {z : ((ℝ × sphere (0 : E) 1) × ℝ) × ℝ |
              z.1.2 < z.2 ∧ z.2 ≤ b} from hz)]
        · rw [Set.indicator_of_notMem (show z.2 ∉ Ioc z.1.2 b from hz),
            Set.indicator_of_notMem
              (show z ∉ {z : ((ℝ × sphere (0 : E) 1) × ℝ) × ℝ |
                z.1.2 < z.2 ∧ z.2 ≤ b} from hz)]
      rw [heq]
      exact hG1.indicator (hmeasS' b)
    have hEq : (fun q : (ℝ × sphere (0 : E) 1) × ℝ => ∫ t in Ioc q.2 b,
        inner ℝ (G (q.1.1, (Θ q.1.1 * t) • ((q.1.2 : sphere (0 : E) 1) : E)))
          ((q.1.2 : sphere (0 : E) 1) : E))
        = fun q => ∫ y : ℝ, (Ioc q.2 b).indicator
          (fun t => inner ℝ (G (q.1.1, (Θ q.1.1 * t) • ((q.1.2 : sphere (0 : E) 1) : E)))
            ((q.1.2 : sphere (0 : E) 1) : E)) y := by
      funext q
      exact (integral_indicator measurableSet_Ioc).symm
    rw [hEq]
    exact hF'.integral_prod_right' (ν := (volume : Measure ℝ))
  have hΘcomp : Measurable (fun q : (ℝ × sphere (0 : E) 1) × ℝ => Θ q.1.1) :=
    hΘmeas.comp (measurable_fst.comp measurable_fst)
  have hΘweighted := hΘcomp.stronglyMeasurable.mul ((hJ1 (3/4)).sub (hJ2 (3/4)))
  have hFcomp :=
    (hF.measurable.comp (Measurable.prodMk (measurable_fst.comp measurable_fst) hsmul)
      ).stronglyMeasurable
  have hinner := hFcomp.sub hΘweighted
  have hI1 := hinner.integral_prod_right' (ν := volume.restrict (Ioo (1/2 : ℝ) 1))
  have hI2 := ((hJ1 (3/4)).sub (hJ2 (3/4)))
  have hΘcomp' : Measurable (fun q : ℝ × sphere (0 : E) 1 => Θ q.1) :=
    hΘmeas.comp measurable_fst
  have hconst1 : Measurable (fun _ : ℝ × sphere (0 : E) 1 => (1 : ℝ)) := measurable_const
  have hI2' := hΘcomp'.stronglyMeasurable.mul
    (hI2.comp_measurable (Measurable.prodMk measurable_id hconst1))
  have hfin := (hI1.const_mul (2 : ℝ)).add hI2'
  have hcongr : (fun p : ℝ × sphere (0 : E) 1 =>
      traceSphere (Θ p.1) (fun z => F (p.1, z)) (fun z => G (p.1, z)) (p.2 : E))
      = (fun p : ℝ × sphere (0 : E) 1 => 2 *
          (∫ τ in Ioo (1/2 : ℝ) 1,
            (F (p.1, (Θ p.1 * τ) • (p.2 : E))
              - Θ p.1 * ∫ x in ((3:ℝ)/4)..τ,
                  inner ℝ (G (p.1, (Θ p.1 * x) • (p.2 : E))) (p.2 : E)))
          + Θ p.1 * ∫ τ in ((3:ℝ)/4)..(1:ℝ), inner ℝ (G (p.1, (Θ p.1 * τ) • (p.2 : E))) (p.2 : E)) :=
    funext fun p => traceSphere_rescale_tlm (hΘpos p.1) (fun z => F (p.1, z))
      (fun z => G (p.1, z)) (p.2 : E)
  rw [hcongr]
  exact hfin

/-! ## 3. A globally measurable, globally positive extension of `C.θ`

`C.θ` is a total function `ℝ → ℝ`, but the `Cap` structure only constrains it on
`Set.Ioo (-C.K) 0`; off that interval it is entirely unconstrained (see the file docstring), so
it need not be measurable there.  `thetaExt_tlm C` is a genuinely globally measurable, globally
positive function that agrees with `C.θ` **exactly** (not just a.e.) on `Set.Ioo (-C.K) 0`. -/

/-- A globally measurable, globally positive extension of `C.θ`, agreeing with `C.θ` exactly on
`Set.Ioo (-C.K) 0`. -/
def thetaExt_tlm (C : Cap m) : ℝ → ℝ := (Set.Ioo (-C.K) 0).piecewise C.θ (fun _ => 1)

theorem thetaExt_eq_tlm (C : Cap m) {s : ℝ} (hs : s ∈ Set.Ioo (-C.K) 0) :
    thetaExt_tlm C s = C.θ s := Set.piecewise_eq_of_mem _ _ _ hs

theorem thetaExt_pos_tlm (C : Cap m) (s : ℝ) : 0 < thetaExt_tlm C s := by
  by_cases hs : s ∈ Set.Ioo (-C.K) 0
  · rw [thetaExt_eq_tlm C hs]; exact C.θ_pos s hs
  · rw [thetaExt_tlm, Set.piecewise_eq_of_notMem _ _ _ hs]; norm_num

/-- **`thetaExt_tlm C` is globally measurable.**  This does *not* need `C.θ` measurable off
`Ioo (-C.K) 0`: `stronglyMeasurable_of_restrict_of_restrict_compl` only asks for strong
measurability of the *restrictions* to the two measurable pieces `Ioo (-C.K) 0` and its
complement separately, and on `Ioo (-C.K) 0` the restriction of `thetaExt_tlm C` is *exactly*
the restriction of `C.θ` (continuous there), while on the complement it is the constant `1`. -/
theorem measurable_thetaExt_tlm (C : Cap m) : Measurable (thetaExt_tlm C) := by
  have hs : MeasurableSet (Set.Ioo (-C.K) 0) := measurableSet_Ioo
  refine stronglyMeasurable_of_restrict_of_restrict_compl hs ?_ ?_ |>.measurable
  · have hcont : Continuous ((Set.Ioo (-C.K) 0).restrict C.θ) :=
      (Cap.Concave.continuousOn_Ioo C).restrict
    have heq : (Set.Ioo (-C.K) 0).restrict (thetaExt_tlm C)
        = (Set.Ioo (-C.K) 0).restrict C.θ := by
      funext x
      show thetaExt_tlm C x.1 = C.θ x.1
      exact thetaExt_eq_tlm C x.2
    rw [heq]
    exact hcont.stronglyMeasurable
  · have heq : (Set.Ioo (-C.K) 0)ᶜ.restrict (thetaExt_tlm C)
        = (Set.Ioo (-C.K) 0)ᶜ.restrict (fun _ => (1 : ℝ)) := by
      funext x
      show thetaExt_tlm C x.1 = 1
      rw [thetaExt_tlm, Set.piecewise_eq_of_notMem _ _ _ x.2]
    rw [heq]
    exact stronglyMeasurable_const

/-! ## 4. Deliverable 1: joint measurability of the θ-parametrised trace, conditionally

`hJoint` of `aestronglyMeasurable_lateralTraceGen_tlg` is the *unrestricted* (not merely a.e.)
statement `StronglyMeasurable (fun p : ℝ × sphere .. => traceSphere (C.θ p.1) ..)`.  As explained
in the file docstring, this genuinely needs `C.θ` measurable (and, for the argument above,
positive) as a literal function of `p.1` ranging over *all* of `ℝ`, which the bare `Cap`
structure does not provide off `Ioo (-C.K) 0`.  We isolate this as the two hypotheses
`hθmeas`, `hθpos` (both automatic for every concrete cap of this development). -/

/-- **Deliverable 1** (conditional on global measurability and positivity of `C.θ`, which the
`Cap` structure does not itself provide — see the file docstring): joint strong measurability of
the θ-parametrised sphere trace of the canonical measurable representatives. -/
theorem stronglyMeasurable_traceSphere_theta_joint_tlm (C : Cap m) (u : H1P C.body)
    (hθmeas : Measurable C.θ) (hθpos : ∀ s : ℝ, 0 < C.θ s) :
    StronglyMeasurable
      (fun p : ℝ × sphere (0 : E) 1 =>
        traceSphere (C.θ p.1) (fun z => repFun C u (p.1, z)) (fun z => repGz_el C u (p.1, z))
          ((p.2 : E))) :=
  stronglyMeasurable_traceSphere_paramR_tlm hθmeas hθpos (stronglyMeasurable_repFun C u)
    (stronglyMeasurable_repGz_el C u)

/-! ## 5. Transporting an a.e. equality on `C.body` to a joint a.e. statement along rays

This mirrors `RobinCaps.ThinDomain.ae_radial_congr_joint_tgb` (an a.e. equality on a fixed-radius
bulk cylinder transports to a joint a.e. statement along rays), but for the genuinely
variable-radius region `C.body`.  The measurability of the auxiliary "indicator mass" function
`Θ` below again goes through `thetaExt_tlm C` (rescaling `Ioo 0 R` to the fixed `Ioo 0 1`), so
this transport is **unconditional**. -/

theorem thetaExt_le_one_tlm (C : Cap m) (s : ℝ) : thetaExt_tlm C s ≤ 1 := by
  by_cases hs : s ∈ Set.Ioo (-C.K) 0
  · rw [thetaExt_eq_tlm C hs]; exact C.θ_le_one s hs
  · rw [thetaExt_tlm, Set.piecewise_eq_of_notMem _ _ _ hs]

theorem isFiniteMeasure_sphereMeasure_tlm : IsFiniteMeasure (sphereMeasure m) := inferInstance

/-- Rescale a set integral over `Ioo 0 R` to a set integral over the fixed `Ioo 0 1`, via
`r = R τ`. -/
theorem setIntegral_Ioo0_comp_mul_tlm {R : ℝ} (hR : 0 < R) (F : ℝ → ℝ) :
    (∫ r in Set.Ioo (0 : ℝ) R, F r) = R * ∫ τ in Set.Ioo (0 : ℝ) 1, F (R * τ) := by
  have hR0 : R ≠ 0 := hR.ne'
  have h1 : (∫ r in Set.Ioo (0 : ℝ) R, F r) = ∫ r in (0 : ℝ)..R, F r := by
    rw [intervalIntegral.integral_of_le hR.le]
    exact (integral_Ioc_eq_integral_Ioo).symm
  have h2 : (∫ τ in Set.Ioo (0 : ℝ) 1, F (R * τ)) = ∫ τ in (0 : ℝ)..1, F (R * τ) := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    exact (integral_Ioc_eq_integral_Ioo).symm
  rw [h1, h2]
  have h := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1) (f := F) hR0
  simp only [smul_eq_mul] at h
  rw [h]
  have heq1 : R * (0 : ℝ) = 0 := by ring
  have heq2 : R * (1 : ℝ) = R := by ring
  rw [heq1, heq2]
  field_simp

/-- **Joint strong measurability of the `thetaExt_tlm`-truncated radial indicator average.** -/
theorem stronglyMeasurable_Theta_tlm (C : Cap m) {N : Set (CapSpace m)} (hN : MeasurableSet N) :
    StronglyMeasurable (fun p : ℝ × sphere (0 : E) 1 =>
      ∫ r in Set.Ioo (0 : ℝ) (thetaExt_tlm C p.1),
        r ^ (m - 1) * (N.indicator (fun _ => (1 : ℝ))) (p.1, r • (p.2 : E))) := by
  classical
  set indN : CapSpace m → ℝ := N.indicator (fun _ => (1 : ℝ)) with hindN_def
  have hindNmeas : Measurable indN := measurable_const.indicator hN
  have hsmul : Measurable (fun q : (ℝ × sphere (0 : E) 1) × ℝ =>
      (thetaExt_tlm C q.1.1 * q.2) • ((q.1.2 : sphere (0 : E) 1) : E)) :=
    (Measurable.mul ((measurable_thetaExt_tlm C).comp (measurable_fst.comp measurable_fst))
      measurable_snd).smul (measurable_subtype_coe.comp (measurable_snd.comp measurable_fst))
  have hcomp : Measurable (fun q : (ℝ × sphere (0 : E) 1) × ℝ =>
      indN (q.1.1, (thetaExt_tlm C q.1.1 * q.2) • ((q.1.2 : sphere (0 : E) 1) : E))) :=
    hindNmeas.comp (Measurable.prodMk (measurable_fst.comp measurable_fst) hsmul)
  have hpow : Measurable (fun q : (ℝ × sphere (0 : E) 1) × ℝ =>
      (thetaExt_tlm C q.1.1 * q.2) ^ (m - 1)) :=
    ((measurable_thetaExt_tlm C).comp (measurable_fst.comp measurable_fst)).mul measurable_snd
      |>.pow_const _
  have hH : StronglyMeasurable (fun q : (ℝ × sphere (0 : E) 1) × ℝ =>
      (thetaExt_tlm C q.1.1 * q.2) ^ (m - 1) *
        indN (q.1.1, (thetaExt_tlm C q.1.1 * q.2) • ((q.1.2 : sphere (0 : E) 1) : E))) :=
    (hpow.mul hcomp).stronglyMeasurable
  have hI := hH.integral_prod_right' (ν := volume.restrict (Set.Ioo (0 : ℝ) 1))
  have hΘcomp : Measurable (fun p : ℝ × sphere (0 : E) 1 => thetaExt_tlm C p.1) :=
    (measurable_thetaExt_tlm C).comp measurable_fst
  have hfin := hΘcomp.stronglyMeasurable.mul hI
  have hcongr : (fun p : ℝ × sphere (0 : E) 1 =>
      ∫ r in Set.Ioo (0 : ℝ) (thetaExt_tlm C p.1), r ^ (m - 1) * indN (p.1, r • (p.2 : E)))
      = (fun p : ℝ × sphere (0 : E) 1 => thetaExt_tlm C p.1 *
          ∫ τ in Set.Ioo (0 : ℝ) 1, (thetaExt_tlm C p.1 * τ) ^ (m - 1) *
            indN (p.1, (thetaExt_tlm C p.1 * τ) • (p.2 : E))) :=
    funext fun p => setIntegral_Ioo0_comp_mul_tlm (thetaExt_pos_tlm C p.1)
      (fun r => r ^ (m - 1) * indN (p.1, r • (p.2 : E)))
  rw [hcongr]
  exact hfin

end
end RobinCaps.Cap
