import RobinCaps.ThinDomain.TrialBound
import RobinCaps.Cap.TraceDataHemi
import RobinCaps.ThinDomain.Reflect
import RobinCaps.Sobolev.RadialSlice
import RobinCaps.ThinDomain.SphereSlicing
import RobinCaps.Cap.LowerWeak
import RobinCaps.ThinDomain.H1P
import RobinCaps.ThinDomain.Tensor
import RobinCaps.Compact.Dilation

/-!
# U-TRIALBOUND-W: `lem:cap-upper` for a weak (merely `H¹`) transverse ground state

This file proves the manuscript's `lem:cap-upper` (`eq:upper-gradient`, `eq:upper-J`,
`eq:upper-mass`, `reference/robin_endcaps_corrected_en.tex`, lines 651–685) for a **weak**
transverse ground state `gs : TransverseGroundState m α R bd` (no `C¹` regularity assumed),
replacing the `C¹` version `RobinCaps.ThinDomain.cap_upper_gradient` /
`cap_mass_expansion` / `cap_boundary_expansion` / `cap_upper_J` of `TrialBound.lean`.

## The construction

`Ψ_R = transLift m R gs.psi` is lifted to the cap `𝒞 = C.body` exactly as in the `C¹` case
(constant in the axial variable `s`), but now the lift is built as a genuine element
`capLiftW_tw : H1P C.body` of the *weak* Sobolev space of `H1P.lean`, with axial weak derivative
`0` and transverse weak gradient `transLiftGrad_tw m R gs.psi`, the weak gradient of `Ψ_R` itself.

The construction goes through the already-proved tensor-product weak-gradient lemma
`hasWeakGradP_tensor` / `H1P.tensor` of `RobinCaps/ThinDomain/Tensor.lean` (Fubini in the axial
variable, applied to the constant axial factor `F ≡ 1`) on the *cylinder*
`Ioo (-C.K) 0 ×ˢ ball 0 1`, followed by `HasWeakGradP.mono` to restrict from the cylinder to the
cap body `C.body ⊆` cylinder (`body_subset_cyl`, already proved in `TrialBound.lean`).  The
transverse function itself, `Ψ_R` together with its weak gradient, is obtained from
`gs.psi : TransH1 m R` by the dilation `y ↦ R^{m/2} ψ(Ry)` of `RobinCaps/Compact/Dilation.lean`
(`dilate`, `castRadius`), which is exactly `hasWeakGrad_comp_smul` packaged as an `H¹` element.

## The boundary term, through the trace datum

The boundary integral `∫_Γ Ψ_R² dℋ^m` has **no pointwise meaning** for a merely-`H¹` function, so
it is replaced by `capJtermW_tw := (Cap.capTraceDataHemi_th m hm).bdΓ capLiftW_tw capLiftW_tw`
(`= ∫_{upper half-sphere} (gammaTrace capLiftW_tw)² dσ` by `capTraceDataHemi_bdΓ_eq_th`), on the
**hemisphere** `C = Cap.hemisphere m`.  Its expansion `cap_boundary_expansion_tw` is proved
*without* any pointwise trace or radial trace inequality (`ball_trace_ineq_c1` is not used here):
writing `Ψ_R = c + g` with `c = ω_m^{-1/2}` and `‖g‖²_{H¹(B_1)} ≤ Cexp² R²` (`hexp.psiH1`), the
lift splits as `capLiftW_tw = Cap.constP C c + G` with `G := capLiftW_tw - Cap.constP C c`, and

* `bdΓ` is bilinear (`RobinCaps.Compact.bilin_add_smul_smul`) and its value on the constant `1`
  is `revolutionArea` (`Cap.bdΓ_oneP`), so `bdΓ(constP c, constP c) = c² · revolutionArea =
  ω_m⁻¹ · revolutionArea`;
* the diagonal term `bdΓ(G,G) ≤ traceConst · (dirichletP G + massP G)` (`CapTraceData.trace_ineq`)
  is `O(R²)`, since `dirichletP G = dirichletP capLiftW_tw` (`Cap.dirichletP_sub_constP`) is
  bounded by `cap_upper_gradient_tw` and `massP G` by the direct (no-Young's-trick) comparison
  `setIntegral_body_le_tw`;
* the cross term `bdΓ(constP c, G)` is bounded by Cauchy–Schwarz for the nonnegative symmetric
  form `bdΓ` (`RobinCaps.Compact.bilin_cauchy_schwarz`): `bdΓ(constP c,G)² ≤ bdΓ(constP c,constP c)
  · bdΓ(G,G)`, giving an `O(R)` bound (both `O(R²)` factors turn into a single `O(R)` factor under
  the square root, since `√(R²) = R` for `R ≥ 0`).

## Contents

* `transLiftGrad_tw`, `psiUnit_tw`, `transLiftH1_tw` — the weak gradient of `Ψ_R` on `B_m(1)`,
  built from `RobinCaps.Compact.dilate`/`castRadius`;
* `capLiftW_tw` — the resulting element of `H1P C.body`;
* `ExpW_tw` (and the weaker `ExpW_tw_weak`) — the hypothesis structure recording
  `lem:transverse`'s expansions for a weak ground state;
* `cap_upper_gradient_tw`, `cap_mass_le_tw`, `cap_mass_expansion_tw`, `cap_boundary_expansion_tw`,
  `cap_upper_J_tw` — the five statements of `lem:cap-upper`, weak version;
* `capEnergyTermW_tw`, `capEnergyTermW_sub_beta_tw` — the assembled cap-level energy correction.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Metric Filter

open scoped ENNReal Topology InnerProductSpace ContDiff

namespace RobinCaps.ThinDomain

open RobinCaps.Sobolev RobinCaps.Domain

noncomputable section

/-! ## 1. The weak gradient of the lifted transverse ground state on `B_m(1)` -/

variable {m : ℕ} {R : ℝ}

/-- The weak gradient of `transLift m R ψ` on `B_m(1)`, i.e. the analogue of
`classicalGrad_transLift` for a merely-`H¹` (not `C¹`) transverse state `ψ`. -/
def transLiftGrad_tw (m : ℕ) (R : ℝ) (ψ : TransH1 m R) (y : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) :=
  (R ^ ((m : ℝ) / 2) * R) • ψ.grad (R • y)

/-- The unnormalised dilation `y ↦ ψ(Ry)` of `ψ`, transported to the unit ball, as an element of
`Weak.H1 (ball 0 1)`.  Built from `RobinCaps.Compact.dilate`/`castRadius`. -/
def psiUnit_tw (hR : 0 < R) (ψ : TransH1 m R) :
    Weak.H1 (ball (0 : EuclideanSpace ℝ (Fin m)) 1) :=
  RobinCaps.Compact.castRadius (div_self hR.ne') (RobinCaps.Compact.dilate R hR ψ)

theorem psiUnit_tw_toFun (hR : 0 < R) (ψ : TransH1 m R) :
    (psiUnit_tw hR ψ).toFun = fun y => ψ.toFun (R • y) := by
  unfold psiUnit_tw
  rw [RobinCaps.Compact.castRadius_toFun, RobinCaps.Compact.dilate_toFun]

theorem psiUnit_tw_grad (hR : 0 < R) (ψ : TransH1 m R) :
    (psiUnit_tw hR ψ).grad = fun y => R • ψ.grad (R • y) := by
  unfold psiUnit_tw
  rw [RobinCaps.Compact.castRadius_grad, RobinCaps.Compact.dilate_grad]

/-- `Ψ_R = R^{m/2} ψ(R·)` together with its weak gradient, as an element of
`Weak.H1 (ball 0 1)`. -/
def transLiftH1_tw (hR : 0 < R) (ψ : TransH1 m R) :
    Weak.H1 (ball (0 : EuclideanSpace ℝ (Fin m)) 1) :=
  (R ^ ((m : ℝ) / 2)) • psiUnit_tw hR ψ

theorem transLiftH1_tw_toFun (hR : 0 < R) (ψ : TransH1 m R) :
    (transLiftH1_tw hR ψ).toFun = transLift m R ψ := by
  funext y
  show (R ^ ((m : ℝ) / 2)) • (psiUnit_tw hR ψ).toFun y = transLift m R ψ y
  rw [psiUnit_tw_toFun]
  show (R ^ ((m : ℝ) / 2)) * ψ.toFun (R • y) = transLift m R ψ y
  rfl

theorem transLiftH1_tw_grad (hR : 0 < R) (ψ : TransH1 m R) :
    (transLiftH1_tw hR ψ).grad = transLiftGrad_tw m R ψ := by
  funext y
  show (R ^ ((m : ℝ) / 2)) • (psiUnit_tw hR ψ).grad y = transLiftGrad_tw m R ψ y
  rw [psiUnit_tw_grad]
  show (R ^ ((m : ℝ) / 2)) • (R • ψ.grad (R • y)) = transLiftGrad_tw m R ψ y
  rw [smul_smul]
  rfl

theorem memLp_transLift_tw (hR : 0 < R) (ψ : TransH1 m R) :
    MemLp (transLift m R ψ) 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)) := by
  have h := (transLiftH1_tw hR ψ).memL2
  rwa [transLiftH1_tw_toFun] at h

theorem memLp_transLiftGrad_tw (hR : 0 < R) (ψ : TransH1 m R) :
    MemLp (transLiftGrad_tw m R ψ) 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)) := by
  have h := (transLiftH1_tw hR ψ).grad_memL2
  rwa [transLiftH1_tw_grad] at h

/-! ## 2. The lifted cap function, as a genuine element of `H1P C.body` -/

/-- The tensor lift of `transLiftH1_tw` to the cylinder `Ioo (-C.K) 0 ×ˢ ball 0 1`, constant in
the axial direction (`F ≡ 1`).  Fubini in the axial variable (`hasWeakGradP_tensor`) supplies its
weak gradient. -/
def capCylTensor_tw (C : Cap m) (hR : 0 < R) (ψ : TransH1 m R) :
    H1P (bulkCyl (-C.K) 0 m 1) :=
  H1P.tensor (fun _ : ℝ => (1 : ℝ)) contDiff_const (by linarith [C.hK] : -C.K < (0:ℝ))
    (transLiftH1_tw hR ψ)

theorem capBody_subset_bulkCyl (C : Cap m) :
    C.body ⊆ bulkCyl (-C.K) 0 m 1 := by
  rw [bulkCyl_eq]; exact body_subset_cyl C

theorem capCylTensor_tw_toFun_eq (C : Cap m) (hR : 0 < R) (ψ : TransH1 m R) :
    (capCylTensor_tw C hR ψ).toFun = fun p : CapSpace m => transLift m R ψ p.2 := by
  funext p
  show tensorFun (fun _ : ℝ => (1 : ℝ)) (transLiftH1_tw hR ψ) p = transLift m R ψ p.2
  rw [tensorFun_apply, one_mul, transLiftH1_tw_toFun]

theorem capCylTensor_tw_gx_eq (C : Cap m) (hR : 0 < R) (ψ : TransH1 m R) :
    (capCylTensor_tw C hR ψ).gx = fun _ : CapSpace m => (0 : ℝ) := by
  funext p
  show deriv (fun _ : ℝ => (1 : ℝ)) p.1 * (transLiftH1_tw hR ψ).toFun p.2 = 0
  rw [deriv_const]; ring

theorem capCylTensor_tw_gz_eq (C : Cap m) (hR : 0 < R) (ψ : TransH1 m R) :
    (capCylTensor_tw C hR ψ).gz = fun p : CapSpace m => transLiftGrad_tw m R ψ p.2 := by
  funext p
  show (fun _ : ℝ => (1 : ℝ)) p.1 • (transLiftH1_tw hR ψ).grad p.2 = transLiftGrad_tw m R ψ p.2
  rw [one_smul, transLiftH1_tw_grad]

/-- **The lifted transverse ground state, as an element of `H1P C.body`.**  Its underlying
function is `Ψ_R = transLift m R ψ` (independent of the axial variable `s`), its axial weak
derivative is `0`, and its transverse weak gradient is `transLiftGrad_tw m R ψ`. -/
def capLiftW_tw (C : Cap m) (hR : 0 < R) (ψ : TransH1 m R) : H1P C.body where
  toFun := fun p => transLift m R ψ p.2
  gx := fun _ => 0
  gz := fun p => transLiftGrad_tw m R ψ p.2
  memL2 := by
    have h := (capCylTensor_tw C hR ψ).memL2
    rw [capCylTensor_tw_toFun_eq] at h
    exact h.mono_measure (Measure.restrict_mono_set volume (capBody_subset_bulkCyl C))
  gx_memL2 := by
    have h := (capCylTensor_tw C hR ψ).gx_memL2
    rw [capCylTensor_tw_gx_eq] at h
    exact h.mono_measure (Measure.restrict_mono_set volume (capBody_subset_bulkCyl C))
  gz_memL2 := by
    have h := (capCylTensor_tw C hR ψ).gz_memL2
    rw [capCylTensor_tw_gz_eq] at h
    exact h.mono_measure (Measure.restrict_mono_set volume (capBody_subset_bulkCyl C))
  hasWeakGrad := by
    have h := (capCylTensor_tw C hR ψ).hasWeakGrad
    rw [show (capCylTensor_tw C hR ψ).toFun = fun p : CapSpace m => transLift m R ψ p.2
        from capCylTensor_tw_toFun_eq C hR ψ,
      show (capCylTensor_tw C hR ψ).gx = fun _ : CapSpace m => (0 : ℝ)
        from capCylTensor_tw_gx_eq C hR ψ,
      show (capCylTensor_tw C hR ψ).gz = fun p : CapSpace m => transLiftGrad_tw m R ψ p.2
        from capCylTensor_tw_gz_eq C hR ψ] at h
    exact HasWeakGradP.mono (capBody_subset_bulkCyl C) h

@[simp] theorem capLiftW_tw_toFun (C : Cap m) (hR : 0 < R) (ψ : TransH1 m R) (p : CapSpace m) :
    (capLiftW_tw C hR ψ).toFun p = transLift m R ψ p.2 := rfl

@[simp] theorem capLiftW_tw_gx (C : Cap m) (hR : 0 < R) (ψ : TransH1 m R) (p : CapSpace m) :
    (capLiftW_tw C hR ψ).gx p = 0 := rfl

@[simp] theorem capLiftW_tw_gz (C : Cap m) (hR : 0 < R) (ψ : TransH1 m R) (p : CapSpace m) :
    (capLiftW_tw C hR ψ).gz p = transLiftGrad_tw m R ψ p.2 := rfl

/-! ## 3. Two Fubini-free integral comparisons on the cap body, for merely-integrable
transverse integrands (the `MemLp`/`IntegrableOn` analogues of `TrialBound.setIntegral_body_le`
and `abs_setIntegral_body_le`, which needed continuity). -/

theorem integrableOn_snd_cyl_tw (C : Cap m) {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf : IntegrableOn f (ball (0 : EuclideanSpace ℝ (Fin m)) 1)) :
    IntegrableOn (fun p : CapSpace m => f p.2)
      (Ioo (-C.K) 0 ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) 1) := by
  haveI hfin : IsFiniteMeasure (volume.restrict (Ioo (-C.K) (0 : ℝ))) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioo]; exact ENNReal.ofReal_lt_top⟩
  have h1 : Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin m) => f p.2)
      ((volume.restrict (Ioo (-C.K) (0 : ℝ))).prod
        (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1))) :=
    hf.comp_snd (volume.restrict (Ioo (-C.K) (0 : ℝ)))
  rwa [Measure.prod_restrict, ← Measure.volume_eq_prod] at h1

/-- **The cap sits in the unit cylinder**, weak version: for a nonnegative transverse function
merely integrable on `B_m(1)`, `∫_𝒞 f(z) ≤ K ∫_{B_m(1)} f`. -/
theorem setIntegral_body_le_tw (C : Cap m) {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf : IntegrableOn f (ball (0 : EuclideanSpace ℝ (Fin m)) 1)) (hf0 : ∀ y, 0 ≤ f y) :
    (∫ p in C.body, f p.2) ≤ C.K * ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, f y := by
  have h1 : (∫ p in C.body, f p.2)
      ≤ ∫ p in Ioo (-C.K) 0 ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) 1, f p.2 :=
    setIntegral_mono_set (integrableOn_snd_cyl_tw C hf)
      (Filter.Eventually.of_forall fun p => hf0 _) (body_subset_cyl C).eventuallyLE
  rwa [setIntegral_cyl_snd C f] at h1

theorem abs_setIntegral_body_le_tw (C : Cap m) {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf : IntegrableOn f (ball (0 : EuclideanSpace ℝ (Fin m)) 1)) :
    |∫ p in C.body, f p.2| ≤ C.K * ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, |f y| := by
  have h0 : |∫ p in C.body, f p.2| ≤ ∫ p in C.body, |f p.2| := by
    simpa only [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (μ := volume.restrict C.body)
        (f := fun p : CapSpace m => f p.2)
  exact h0.trans (setIntegral_body_le_tw C hf.abs fun y => abs_nonneg _)

/-- The weak (`MemLp`-based) analogue of `TrialBound.integral_abs_sq_sub_le`, specialised to
`r = 1` (the only radius needed once the boundary term is routed through the trace datum). -/
theorem integral_abs_sq_sub_le_tw (m : ℕ) (hm : 1 ≤ m) {Ψ : EuclideanSpace ℝ (Fin m) → ℝ}
    (hΨ : MemLp Ψ 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)))
    {c R : ℝ} (hc : 0 ≤ c) (hR : 0 < R) :
    (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, |Ψ y ^ 2 - c ^ 2|)
      ≤ (1 + c / R) * (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, (Ψ y - c) ^ 2)
        + c * R * omega m := by
  have hΨsq : IntegrableOn (fun y => Ψ y ^ 2) (ball (0 : EuclideanSpace ℝ (Fin m)) 1) :=
    hΨ.integrable_sq
  have hΨcsq : IntegrableOn (fun y => (Ψ y - c) ^ 2) (ball (0 : EuclideanSpace ℝ (Fin m)) 1) :=
    (hΨ.sub (memLp_const c)).integrable_sq
  have h1 : (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, |Ψ y ^ 2 - c ^ 2|)
      ≤ ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
          ((1 + c / R) * (Ψ y - c) ^ 2 + c * R) :=
    setIntegral_mono_on (hΨsq.sub (integrable_const (c ^ 2))).abs
      ((hΨcsq.const_mul _).add (integrable_const _)) measurableSet_ball
      fun y _ => abs_sq_sub_sq_le hc hR
  have h2 : (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
      ((1 + c / R) * (Ψ y - c) ^ 2 + c * R))
      = (1 + c / R) * (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, (Ψ y - c) ^ 2)
        + c * R * omega m := by
    rw [integral_add (hΨcsq.const_mul _) (integrable_const _), integral_const_mul,
      setIntegral_const, measureReal_def, volume_ball_toReal m hm zero_le_one, smul_eq_mul]
    ring
  linarith [h1, h2]

/-! ## 4. The hypothesis structure: the transverse expansions of `lem:transverse`, weak
version -/

variable {α : ℝ} {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}

/-- **The transverse expansions** for a *weak* ground state `gs : TransverseGroundState m α R
bd` (no `C¹` regularity), with `‖Ψ_R − ω_m^{-1/2}‖²_{H¹(B_m(1))} ≤ Cexp² R²` — the primary,
manuscript-scale form of `eq:Psi-H1`, needed in particular so that the `R⁻¹`-weighted gradient
term of `capEnergyTermW_tw` stays bounded as `R → 0`.  `dR_close`, `dR_ge`, `nuExp` mirror
`TrialBound.TransverseExpansionData` verbatim. -/
structure ExpW_tw (m : ℕ) (α R : ℝ) {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}
    (gs : TransverseGroundState m α R bd) (Cexp : ℝ) : Prop where
  /-- `eq:Psi-H1`, weak form: `‖Ψ_R − ω_m^{-1/2}‖²_{H¹(B_m(1))} ≤ Cexp² R²`. -/
  psiH1 : (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
        (transLift m R gs.psi y - (Real.sqrt (omega m))⁻¹) ^ 2)
      + (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
          ‖transLiftGrad_tw m R gs.psi y‖ ^ 2) ≤ Cexp ^ 2 * R ^ 2
  /-- `eq:d-R`, first half. -/
  dR_close : |(∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
      - Real.sqrt (omega m)| ≤ Cexp * R
  /-- `eq:d-R`, second half. -/
  dR_ge : Real.sqrt (omega m) / 2
      ≤ ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y
  /-- `eq:nu-expansion`. -/
  nuExp : |R ^ 2 * gs.nu - (m : ℝ) * α * R| ≤ Cexp * R ^ 2

/-- **The weaker variant of `eq:Psi-H1`**, `‖Ψ_R − ω_m^{-1/2}‖²_{H¹(B_m(1))} ≤ Cexp² R`, kept in
case only this power is available from `lem:transverse`.  Every `ExpW_tw` is an `ExpW_tw_weak`
(`ExpW_tw.weaken`, using `R² ≤ R` for `0 < R ≤ 1`); the converse fails, and results that need the
`R²` scaling (`cap_upper_gradient_tw`, `cap_boundary_expansion_tw`,
`capEnergyTermW_sub_beta_tw`) are stated for `ExpW_tw`, not for this weaker structure. -/
structure ExpW_tw_weak (m : ℕ) (α R : ℝ) {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}
    (gs : TransverseGroundState m α R bd) (Cexp : ℝ) : Prop where
  psiH1 : (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
        (transLift m R gs.psi y - (Real.sqrt (omega m))⁻¹) ^ 2)
      + (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
          ‖transLiftGrad_tw m R gs.psi y‖ ^ 2) ≤ Cexp ^ 2 * R
  dR_close : |(∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
      - Real.sqrt (omega m)| ≤ Cexp * R
  dR_ge : Real.sqrt (omega m) / 2
      ≤ ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y
  nuExp : |R ^ 2 * gs.nu - (m : ℝ) * α * R| ≤ Cexp * R ^ 2

theorem ExpW_tw.weaken {gs : TransverseGroundState m α R bd} {Cexp : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (hexp : ExpW_tw m α R gs Cexp) :
    ExpW_tw_weak m α R gs Cexp where
  psiH1 := by
    have hR2 : R ^ 2 ≤ R := by nlinarith [hR.le, hR1]
    have h0 : (0:ℝ) ≤ Cexp ^ 2 := sq_nonneg _
    nlinarith [hexp.psiH1, mul_le_mul_of_nonneg_left hR2 h0]
  dR_close := hexp.dR_close
  dR_ge := hexp.dR_ge
  nuExp := hexp.nuExp

variable {gs : TransverseGroundState m α R bd} {Cexp : ℝ}

theorem ExpW_tw.l2_le (hexp : ExpW_tw m α R gs Cexp) :
    (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
      (transLift m R gs.psi y - (Real.sqrt (omega m))⁻¹) ^ 2) ≤ Cexp ^ 2 * R ^ 2 := by
  have h2 : (0 : ℝ) ≤ ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
      ‖transLiftGrad_tw m R gs.psi y‖ ^ 2 :=
    setIntegral_nonneg measurableSet_ball fun _ _ => by positivity
  linarith [hexp.psiH1]

theorem ExpW_tw.grad_le (hexp : ExpW_tw m α R gs Cexp) :
    (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
      ‖transLiftGrad_tw m R gs.psi y‖ ^ 2) ≤ Cexp ^ 2 * R ^ 2 := by
  have h2 : (0 : ℝ) ≤ ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
      (transLift m R gs.psi y - (Real.sqrt (omega m))⁻¹) ^ 2 :=
    setIntegral_nonneg measurableSet_ball fun _ _ => sq_nonneg _
  linarith [hexp.psiH1]

/-! ## 5. `eq:upper-gradient`, weak version -/

/-- **`eq:upper-gradient`**: `∫_𝒞 |∇_zΨ_R|² ≤ K Cexp² R²`. -/
theorem cap_upper_gradient_tw (C : Cap m) (hR : 0 < R) (hexp : ExpW_tw m α R gs Cexp) :
    (∫ p in C.body, ‖(capLiftW_tw C hR gs.psi).gz p‖ ^ 2) ≤ C.K * (Cexp ^ 2 * R ^ 2) := by
  have hint : IntegrableOn (fun y => ‖transLiftGrad_tw m R gs.psi y‖ ^ 2)
      (ball (0 : EuclideanSpace ℝ (Fin m)) 1) :=
    (memLp_transLiftGrad_tw hR gs.psi).norm.integrable_sq
  simp only [capLiftW_tw_gz]
  exact (setIntegral_body_le_tw C hint fun y => by positivity).trans
    (mul_le_mul_of_nonneg_left hexp.grad_le C.hK.le)

theorem dirichletP_capLiftW_tw_eq (C : Cap m) (hR : 0 < R) (ψ : TransH1 m R) :
    dirichletP (capLiftW_tw C hR ψ) = ∫ p in C.body, ‖transLiftGrad_tw m R ψ p.2‖ ^ 2 := by
  unfold dirichletP
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [capLiftW_tw_gx, capLiftW_tw_gz, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_add]

theorem cap_upper_gradient_tw' (C : Cap m) (hR : 0 < R) (hexp : ExpW_tw m α R gs Cexp) :
    dirichletP (capLiftW_tw C hR gs.psi) ≤ C.K * (Cexp ^ 2 * R ^ 2) := by
  rw [dirichletP_capLiftW_tw_eq]
  exact cap_upper_gradient_tw C hR hexp

/-! ## 6. `eq:upper-mass`, weak version -/

/-- `∫_{B_m(1)} Ψ_R² = 1`, the weak analogue of `TrialBound.integral_transLift_sq` (no `C¹`
regularity needed — the original proof never used it either). -/
theorem integral_transLift_sq_tw (hR : 0 < R) (gs : TransverseGroundState m α R bd) :
    (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y ^ 2) = 1 := by
  have h := integral_ball_smul_radius m (R := R) (ρ := 1) hR (fun z => gs.psi.toFun z ^ 2)
  rw [mul_one] at h
  have h2 : (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y ^ 2)
      = R ^ m * ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, gs.psi.toFun (R • y) ^ 2 := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_ball fun y _ => transLift_sq m hR gs.psi y
  rw [h2, ← h]
  exact gs.normalized

/-- **`eq:upper-mass`, crude form**: `∫_𝒞 Ψ_R² ≤ K`. -/
theorem cap_mass_le_tw (hR : 0 < R) (C : Cap m) (gs : TransverseGroundState m α R bd) :
    (∫ p in C.body, (capLiftW_tw C hR gs.psi).toFun p ^ 2) ≤ C.K := by
  have hint : IntegrableOn (fun y => transLift m R gs.psi y ^ 2)
      (ball (0 : EuclideanSpace ℝ (Fin m)) 1) := (memLp_transLift_tw hR gs.psi).integrable_sq
  have h := setIntegral_body_le_tw C hint fun y => sq_nonneg _
  rwa [integral_transLift_sq_tw hR gs, mul_one] at h

theorem cap_mass_nonneg_tw (C : Cap m) (hR : 0 < R) (gs : TransverseGroundState m α R bd) :
    0 ≤ ∫ p in C.body, (capLiftW_tw C hR gs.psi).toFun p ^ 2 :=
  setIntegral_nonneg (measurableSet_capBody C) fun _ _ => sq_nonneg _

theorem massP_capLiftW_tw_eq (C : Cap m) (hR : 0 < R) (ψ : TransH1 m R) :
    massP (capLiftW_tw C hR ψ) = ∫ p in C.body, (capLiftW_tw C hR ψ).toFun p ^ 2 := rfl

/-- **`eq:upper-mass`, sharp form**: `∫_𝒞 Ψ_R² = |𝒞|/ω_m + O(R)`. -/
theorem cap_mass_expansion_tw (hm : 1 ≤ m) (hR : 0 < R) (hR1 : R ≤ 1) (C : Cap m)
    (hexp : ExpW_tw m α R gs Cexp) :
    |(∫ p in C.body, (capLiftW_tw C hR gs.psi).toFun p ^ 2) - (omega m)⁻¹ * C.revolutionVolume|
      ≤ C.K * (Cexp ^ 2 + (Real.sqrt (omega m))⁻¹ * Cexp ^ 2
          + (Real.sqrt (omega m))⁻¹ * omega m) * R := by
  set c : ℝ := (Real.sqrt (omega m))⁻¹ with hcdef
  have hc0 : 0 ≤ c := le_of_lt (inv_pos.2 (sqrt_omega_pos m))
  have hc2 : c ^ 2 = (omega m)⁻¹ := by rw [hcdef]; exact inv_sqrt_omega_sq m
  have hΨmem : MemLp (transLift m R gs.psi) 2
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)) := memLp_transLift_tw hR gs.psi
  have hΨsqInt : IntegrableOn (fun y => transLift m R gs.psi y ^ 2)
      (ball (0 : EuclideanSpace ℝ (Fin m)) 1) := hΨmem.integrable_sq
  have hvol : (volume C.body).toReal = C.revolutionVolume := Cap.volume_body_eq_of_cap m C
  have hs1 : (∫ p in C.body, (transLift m R gs.psi p.2 ^ 2 - c ^ 2))
      = (∫ p in C.body, (capLiftW_tw C hR gs.psi).toFun p ^ 2)
        - (omega m)⁻¹ * C.revolutionVolume := by
    simp only [capLiftW_tw_toFun]
    rw [integral_sub (integrableOn_snd_cyl_tw C hΨsqInt |>.mono_set (body_subset_cyl C))
      (integrableOn_snd_cyl_tw C (integrable_const (c ^ 2)) |>.mono_set (body_subset_cyl C)),
      setIntegral_const, measureReal_def, smul_eq_mul, hvol, hc2]
    ring
  have hs2 : |∫ p in C.body, (transLift m R gs.psi p.2 ^ 2 - c ^ 2)|
      ≤ C.K * ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
          |transLift m R gs.psi y ^ 2 - c ^ 2| :=
    abs_setIntegral_body_le_tw C (hΨsqInt.sub (integrable_const (c ^ 2)))
  have hs3 := integral_abs_sq_sub_le_tw m hm hΨmem (c := c) (R := R) hc0 hR
  have hs4 := hexp.l2_le
  rw [← hcdef] at hs4
  have hpos : (0 : ℝ) ≤ 1 + c / R := by positivity
  have hA : (1 + c / R) * (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
      (transLift m R gs.psi y - c) ^ 2) ≤ (1 + c / R) * (Cexp ^ 2 * R ^ 2) :=
    mul_le_mul_of_nonneg_left hs4 hpos
  have hB : (1 + c / R) * (Cexp ^ 2 * R ^ 2) = Cexp ^ 2 * R ^ 2 + c * Cexp ^ 2 * R := by
    field_simp
  have hR2 : R ^ 2 ≤ R := by nlinarith [hR.le, hR1]
  have hR2mul : Cexp ^ 2 * R ^ 2 ≤ Cexp ^ 2 * R :=
    mul_le_mul_of_nonneg_left hR2 (sq_nonneg _)
  have hcomb : (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
      |transLift m R gs.psi y ^ 2 - c ^ 2|)
      ≤ (Cexp ^ 2 + c * Cexp ^ 2 + c * omega m) * R := by
    nlinarith [hs3, hA, hB, hR2mul]
  rw [← hs1]
  calc |∫ p in C.body, (transLift m R gs.psi p.2 ^ 2 - c ^ 2)|
      ≤ C.K * ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
          |transLift m R gs.psi y ^ 2 - c ^ 2| := hs2
    _ ≤ C.K * ((Cexp ^ 2 + c * Cexp ^ 2 + c * omega m) * R) :=
        mul_le_mul_of_nonneg_left hcomb C.hK.le
    _ = C.K * (Cexp ^ 2 + c * Cexp ^ 2 + c * omega m) * R := by ring

/-! ## 7. The boundary term, through the trace datum -/

/-- **The `Γ`-boundary term of `Ψ_R`, through the hemisphere's trace datum**:
`capJtermW_tw = bdΓ(Ψ_R, Ψ_R) = ∫_Γ Ψ_R² dℋ^m` (`Cap.capTraceDataHemi_bdΓ_eq_th`), with no
pointwise trace of `Ψ_R` ever invoked. -/
def capJtermW_tw (hm : 1 ≤ m) (hR : 0 < R) (ψ : TransH1 m R) : ℝ :=
  (Cap.capTraceDataHemi_th m hm).bdΓ (capLiftW_tw (Cap.hemisphere m) hR ψ)
    (capLiftW_tw (Cap.hemisphere m) hR ψ)

theorem capJtermW_tw_nonneg (hm : 1 ≤ m) (hR : 0 < R) (ψ : TransH1 m R) :
    0 ≤ capJtermW_tw hm hR ψ :=
  (Cap.capTraceDataHemi_th m hm).bdΓ_nonneg _

/-- `0 ≤ θ(0)` for the hemisphere (needed by `Cap.bdΓ_oneP`): `θ = Cap.semi 1` is a square root,
hence nonnegative everywhere, in particular at the endpoint `s = 0`. -/
theorem hemisphere_theta0_nonneg_tw (m : ℕ) : 0 ≤ (Cap.hemisphere m).θ 0 :=
  Real.sqrt_nonneg _

/-- **`eq:upper-J`, the boundary part**: `bdΓ(Ψ_R,Ψ_R) = ℋ^m(Γ)/ω_m + O(R)`. -/
theorem cap_boundary_expansion_tw (hm : 1 ≤ m) (hR : 0 < R) (hR1 : R ≤ 1)
    (hexp : ExpW_tw m α R gs Cexp) :
    |capJtermW_tw hm hR gs.psi - (omega m)⁻¹ * (Cap.hemisphere m).revolutionArea|
      ≤ (2 * (Real.sqrt (omega m))⁻¹
            * Real.sqrt ((Cap.hemisphere m).revolutionArea
                * ((Cap.capTraceDataHemi_th m hm).traceConst * (2 * (Cap.hemisphere m).K)))
            * |Cexp|
          + (Cap.capTraceDataHemi_th m hm).traceConst * (2 * (Cap.hemisphere m).K) * Cexp ^ 2)
        * R := by
  set C : Cap m := Cap.hemisphere m with hCdef
  set td := Cap.capTraceDataHemi_th m hm with htddef
  set c : ℝ := (Real.sqrt (omega m))⁻¹ with hcdef
  have hc0 : 0 ≤ c := le_of_lt (inv_pos.2 (sqrt_omega_pos m))
  have hc2 : c ^ 2 = (omega m)⁻¹ := by rw [hcdef]; exact inv_sqrt_omega_sq m
  have hθ0 : 0 ≤ C.θ 0 := hemisphere_theta0_nonneg_tw m
  set U : H1P C.body := capLiftW_tw C hR gs.psi with hUdef
  set G : H1P C.body := U - Cap.constP C c with hGdef
  have hUeq : U = G + c • Cap.oneP C := by
    rw [hGdef, Cap.constP_eq_smul]; abel
  -- `bdΓ(1,1) = revolutionArea`
  have hOneOne : td.bdΓ (Cap.oneP C) (Cap.oneP C) = C.revolutionArea :=
    Cap.bdΓ_oneP C hm hθ0 td
  have hOneOneNonneg : 0 ≤ C.revolutionArea := by rw [← hOneOne]; exact td.bdΓ_nonneg _
  -- `dirichletP G = dirichletP U ≤ K Cexp² R²`
  have hdirGeq : dirichletP G = dirichletP U := by
    rw [hGdef]; exact Cap.dirichletP_sub_constP C U c
  have hdirG : dirichletP G ≤ C.K * (Cexp ^ 2 * R ^ 2) := by
    rw [hdirGeq, hUdef]; exact cap_upper_gradient_tw' C hR hexp
  -- `massP G ≤ K Cexp² R²`
  have hGtoFun : ∀ p, G.toFun p = transLift m R gs.psi p.2 - c := by
    intro p; rw [hGdef, Cap.sub_constP_toFun, hUdef, capLiftW_tw_toFun]
  have hMint : IntegrableOn (fun y => (transLift m R gs.psi y - c) ^ 2)
      (ball (0 : EuclideanSpace ℝ (Fin m)) 1) :=
    ((memLp_transLift_tw hR gs.psi).sub (memLp_const c)).integrable_sq
  have hMG : massP G ≤ C.K * (Cexp ^ 2 * R ^ 2) := by
    have heq : massP G = ∫ p in C.body, (transLift m R gs.psi p.2 - c) ^ 2 := by
      unfold massP
      exact integral_congr_ae (Eventually.of_forall fun p => by
        show G.toFun p ^ 2 = (transLift m R gs.psi p.2 - c) ^ 2
        rw [hGtoFun p])
    rw [heq]
    exact (setIntegral_body_le_tw C hMint fun y => sq_nonneg _).trans
      (mul_le_mul_of_nonneg_left hexp.l2_le C.hK.le)
  -- `bdΓ(G,G) ≤ traceConst (dirichletP G + massP G) ≤ traceConst · 2 K Cexp² R²`
  have hGGnonneg : 0 ≤ td.bdΓ G G := td.bdΓ_nonneg G
  have hGG : td.bdΓ G G ≤ td.traceConst * (2 * C.K) * Cexp ^ 2 * R ^ 2 := by
    have h1 := td.trace_ineq G
    have h2 : dirichletP G + massP G ≤ 2 * (C.K * (Cexp ^ 2 * R ^ 2)) := by
      linarith [hdirG, hMG]
    have h3 : (0 : ℝ) ≤ td.traceConst := td.traceConst_nonneg
    calc td.bdΓ G G ≤ td.traceConst * (dirichletP G + massP G) := h1
      _ ≤ td.traceConst * (2 * (C.K * (Cexp ^ 2 * R ^ 2))) :=
          mul_le_mul_of_nonneg_left h2 h3
      _ = td.traceConst * (2 * C.K) * Cexp ^ 2 * R ^ 2 := by ring
  -- Cauchy–Schwarz cross term `bdΓ(1,G)`
  have hCS := RobinCaps.Compact.bilin_cauchy_schwarz (N := td.bdΓ) td.bdΓ_symm td.bdΓ_nonneg
    (Cap.oneP C) G
  have hCSbound : td.bdΓ (Cap.oneP C) G ^ 2
      ≤ C.revolutionArea * (td.traceConst * (2 * C.K)) * (Cexp * R) ^ 2 := by
    calc td.bdΓ (Cap.oneP C) G ^ 2 ≤ td.bdΓ (Cap.oneP C) (Cap.oneP C) * td.bdΓ G G := hCS
      _ = C.revolutionArea * td.bdΓ G G := by rw [hOneOne]
      _ ≤ C.revolutionArea * (td.traceConst * (2 * C.K) * Cexp ^ 2 * R ^ 2) :=
          mul_le_mul_of_nonneg_left hGG hOneOneNonneg
      _ = C.revolutionArea * (td.traceConst * (2 * C.K)) * (Cexp * R) ^ 2 := by ring
  have hCSabs : |td.bdΓ (Cap.oneP C) G|
      ≤ Real.sqrt (C.revolutionArea * (td.traceConst * (2 * C.K))) * |Cexp| * R := by
    have hK0 : (0 : ℝ) ≤ 2 * C.K := by linarith [C.hK]
    have hκ0 : (0 : ℝ) ≤ C.revolutionArea * (td.traceConst * (2 * C.K)) :=
      mul_nonneg hOneOneNonneg (mul_nonneg td.traceConst_nonneg hK0)
    refine Cap.abs_le_of_sq_le_sq_lw ?_
      (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) hR.le)
    have hsq : Real.sqrt (C.revolutionArea * (td.traceConst * (2 * C.K))) ^ 2
        = C.revolutionArea * (td.traceConst * (2 * C.K)) := Real.sq_sqrt hκ0
    calc td.bdΓ (Cap.oneP C) G ^ 2
        ≤ C.revolutionArea * (td.traceConst * (2 * C.K)) * (Cexp * R) ^ 2 := hCSbound
      _ = Real.sqrt (C.revolutionArea * (td.traceConst * (2 * C.K))) ^ 2 * (|Cexp| * R) ^ 2 := by
          rw [hsq, mul_pow, mul_pow, sq_abs]
      _ = (Real.sqrt (C.revolutionArea * (td.traceConst * (2 * C.K))) * |Cexp| * R) ^ 2 := by
          ring
  -- assemble
  have hexpand := RobinCaps.Compact.bilin_add_smul_smul (Q := td.bdΓ) td.bdΓ_symm G
    (Cap.oneP C) c
  have hJdef : capJtermW_tw hm hR gs.psi = td.bdΓ U U := rfl
  have key : capJtermW_tw hm hR gs.psi - (omega m)⁻¹ * C.revolutionArea
      = td.bdΓ G G + 2 * c * td.bdΓ G (Cap.oneP C) := by
    rw [hJdef, hUeq, hexpand, hOneOne, hc2]; ring
  have hsym : td.bdΓ G (Cap.oneP C) = td.bdΓ (Cap.oneP C) G := td.bdΓ_symm G (Cap.oneP C)
  have htri : |td.bdΓ G G + 2 * c * td.bdΓ G (Cap.oneP C)|
      ≤ td.bdΓ G G + 2 * c * |td.bdΓ (Cap.oneP C) G| := by
    calc |td.bdΓ G G + 2 * c * td.bdΓ G (Cap.oneP C)|
        ≤ |td.bdΓ G G| + |2 * c * td.bdΓ G (Cap.oneP C)| := abs_add_le _ _
      _ = td.bdΓ G G + 2 * c * |td.bdΓ (Cap.oneP C) G| := by
          rw [abs_of_nonneg hGGnonneg, hsym, abs_mul, abs_mul,
            abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_nonneg hc0]
  have hR2 : R ^ 2 ≤ R := by nlinarith [hR.le, hR1]
  rw [key]
  calc |td.bdΓ G G + 2 * c * td.bdΓ G (Cap.oneP C)|
      ≤ td.bdΓ G G + 2 * c * |td.bdΓ (Cap.oneP C) G| := htri
    _ ≤ td.traceConst * (2 * C.K) * Cexp ^ 2 * R ^ 2
        + 2 * c * (Real.sqrt (C.revolutionArea * (td.traceConst * (2 * C.K))) * |Cexp| * R) := by
        have := mul_le_mul_of_nonneg_left hCSabs (by positivity : (0:ℝ) ≤ 2 * c)
        linarith [hGG, this]
    _ ≤ td.traceConst * (2 * C.K) * Cexp ^ 2 * R
        + 2 * c * (Real.sqrt (C.revolutionArea * (td.traceConst * (2 * C.K))) * |Cexp| * R) := by
        have h0 : (0:ℝ) ≤ td.traceConst * (2 * C.K) * Cexp ^ 2 :=
          mul_nonneg (mul_nonneg td.traceConst_nonneg (by linarith [C.hK])) (sq_nonneg _)
        nlinarith [mul_le_mul_of_nonneg_left hR2 h0]
    _ = (2 * c * Real.sqrt (C.revolutionArea * (td.traceConst * (2 * C.K))) * |Cexp|
          + td.traceConst * (2 * C.K) * Cexp ^ 2) * R := by ring

/-! ## 8. The `J`-form and `eq:upper-J` -/

/-- **`eq:J-definition`**, through the trace datum: `J[U] = α bdΓ(U,U) − mα ‖U‖²_{L²(𝒞)}`. -/
noncomputable def capJFormW_tw (hm : 1 ≤ m) (α : ℝ) (hR : 0 < R) (ψ : TransH1 m R) : ℝ :=
  α * capJtermW_tw hm hR ψ - (m : ℝ) * α * massP (capLiftW_tw (Cap.hemisphere m) hR ψ)

/-- `|δ_R| = |R ν_R − m α| ≤ Cexp R` (`eq:nu-expansion`), weak version (identical to
`TrialBound.abs_delta_le`; the argument never used `C¹` regularity). -/
theorem abs_delta_le_tw (hR : 0 < R) (hexp : ExpW_tw m α R gs Cexp) :
    |R * gs.nu - (m : ℝ) * α| ≤ Cexp * R := by
  have h := hexp.nuExp
  have he : R ^ 2 * gs.nu - (m : ℝ) * α * R = R * (R * gs.nu - (m : ℝ) * α) := by ring
  rw [he, abs_mul, abs_of_pos hR] at h
  have h3 : R * |R * gs.nu - (m : ℝ) * α| ≤ R * (Cexp * R) := by nlinarith [h]
  exact le_of_mul_le_mul_left h3 hR

/-- **The explicit constant of `cap_boundary_expansion_tw`.** -/
def capBdryConstW_tw (m : ℕ) (hm : 1 ≤ m) (Cexp : ℝ) : ℝ :=
  2 * (Real.sqrt (omega m))⁻¹
      * Real.sqrt ((Cap.hemisphere m).revolutionArea
          * ((Cap.capTraceDataHemi_th m hm).traceConst * (2 * (Cap.hemisphere m).K)))
      * |Cexp|
    + (Cap.capTraceDataHemi_th m hm).traceConst * (2 * (Cap.hemisphere m).K) * Cexp ^ 2

/-- **The explicit constant of `cap_mass_expansion_tw`**, specialised to `C = Cap.hemisphere m`. -/
def capMassConstW_tw (m : ℕ) (Cexp : ℝ) : ℝ :=
  (Cap.hemisphere m).K * (Cexp ^ 2 + (Real.sqrt (omega m))⁻¹ * Cexp ^ 2
      + (Real.sqrt (omega m))⁻¹ * omega m)

/-- **`eq:upper-J`, weak version**: `J[Ψ_R] − δ_R‖Ψ_R‖²_{L²(𝒞)} = β(𝒞) + O(R)`. -/
theorem cap_upper_J_tw (hm : 1 ≤ m) (hR : 0 < R) (hR1 : R ≤ 1)
    (hexp : ExpW_tw m α R gs Cexp) :
    |capJFormW_tw hm α hR gs.psi
        - (R * gs.nu - (m : ℝ) * α) * massP (capLiftW_tw (Cap.hemisphere m) hR gs.psi)
        - Cap.beta (Cap.hemisphere m) α|
      ≤ (|α| * capBdryConstW_tw m hm Cexp + (m : ℝ) * |α| * capMassConstW_tw m Cexp
          + Cexp * (Cap.hemisphere m).K) * R := by
  set C : Cap m := Cap.hemisphere m with hCdef
  have hJ := cap_boundary_expansion_tw hm hR hR1 hexp
  have hδ := abs_delta_le_tw hR hexp
  have hbeta : Cap.beta C α
      = α * ((omega m)⁻¹ * C.revolutionArea)
        - (m : ℝ) * α * ((omega m)⁻¹ * C.revolutionVolume) := by
    rw [Cap.beta, Cap.F, Cap.revolutionF]
    field_simp
  set MM : ℝ := massP (capLiftW_tw C hR gs.psi) with hMM
  set JJ : ℝ := capJtermW_tw hm hR gs.psi with hJJ
  have hM : |MM - (omega m)⁻¹ * C.revolutionVolume|
      ≤ C.K * (Cexp ^ 2 + (Real.sqrt (omega m))⁻¹ * Cexp ^ 2
          + (Real.sqrt (omega m))⁻¹ * omega m) * R := by
    rw [hMM]; exact cap_mass_expansion_tw hm hR hR1 C hexp
  have hMle : MM ≤ C.K := by rw [hMM]; exact cap_mass_le_tw hR C gs
  have hM0 : 0 ≤ MM := by rw [hMM]; exact cap_mass_nonneg_tw C hR gs
  have hunfold : capJFormW_tw hm α hR gs.psi = α * JJ - (m : ℝ) * α * MM := by
    rw [capJFormW_tw, ← hCdef, ← hJJ, ← hMM]
  have hsplit : capJFormW_tw hm α hR gs.psi
      - (R * gs.nu - (m : ℝ) * α) * MM - Cap.beta C α
      = α * (JJ - (omega m)⁻¹ * C.revolutionArea)
        - (m : ℝ) * α * (MM - (omega m)⁻¹ * C.revolutionVolume)
        - (R * gs.nu - (m : ℝ) * α) * MM := by
    rw [hunfold, hbeta]
    ring
  rw [hsplit]
  have h1 : |α * (JJ - (omega m)⁻¹ * C.revolutionArea)|
      ≤ |α| * (capBdryConstW_tw m hm Cexp * R) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hJ (abs_nonneg _)
  have h2 : |(m : ℝ) * α * (MM - (omega m)⁻¹ * C.revolutionVolume)|
      ≤ (m : ℝ) * |α| * (capMassConstW_tw m Cexp * R) := by
    rw [abs_mul, abs_mul, Nat.abs_cast, capMassConstW_tw]
    exact mul_le_mul_of_nonneg_left hM (by positivity : (0:ℝ) ≤ (m : ℝ) * |α|)
  have h3 : |(R * gs.nu - (m : ℝ) * α) * MM| ≤ Cexp * C.K * R := by
    rw [abs_mul, abs_of_nonneg hM0]
    calc |R * gs.nu - (m : ℝ) * α| * MM ≤ (Cexp * R) * MM :=
          mul_le_mul_of_nonneg_right hδ hM0
      _ ≤ (Cexp * R) * C.K :=
          mul_le_mul_of_nonneg_left hMle (le_trans (abs_nonneg _) hδ)
      _ = Cexp * C.K * R := by ring
  have tri : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := by
    intro x y
    rw [sub_eq_add_neg]
    calc |x + -y| ≤ |x| + |-y| := abs_add_le _ _
      _ = |x| + |y| := by rw [abs_neg]
  have t1 := tri (α * (JJ - (omega m)⁻¹ * C.revolutionArea)
      - (m : ℝ) * α * (MM - (omega m)⁻¹ * C.revolutionVolume))
      ((R * gs.nu - (m : ℝ) * α) * MM)
  have t2 := tri (α * (JJ - (omega m)⁻¹ * C.revolutionArea))
      ((m : ℝ) * α * (MM - (omega m)⁻¹ * C.revolutionVolume))
  linarith [t1, t2, h1, h2, h3]

/-! ## 9. The cap-level energy correction -/

/-- **The cap-level energy term of `eq:trial-energy`**, weak version:
`R⁻¹ ∫_𝒞 |∇_zΨ_R|² + (α bdΓ(Ψ_R,Ψ_R) − mα‖Ψ_R‖²_{L²(𝒞)}) − (R ν_R − mα)‖Ψ_R‖²_{L²(𝒞)}`. -/
noncomputable def capEnergyTermW_tw (hm : 1 ≤ m) (α : ℝ) (hR : 0 < R)
    (gs : TransverseGroundState m α R bd) : ℝ :=
  R⁻¹ * (∫ p in (Cap.hemisphere m).body,
      ‖(capLiftW_tw (Cap.hemisphere m) hR gs.psi).gz p‖ ^ 2)
    + capJFormW_tw hm α hR gs.psi
    - (R * gs.nu - (m : ℝ) * α) * massP (capLiftW_tw (Cap.hemisphere m) hR gs.psi)

/-- **`capEnergyTermW_tw` converges to `β(𝒞)` at rate `O(R)`.** -/
theorem capEnergyTermW_sub_beta_tw (hm : 1 ≤ m) (hR : 0 < R) (hR1 : R ≤ 1)
    (hexp : ExpW_tw m α R gs Cexp) :
    |capEnergyTermW_tw hm α hR gs - Cap.beta (Cap.hemisphere m) α|
      ≤ ((Cap.hemisphere m).K * Cexp ^ 2
          + (|α| * capBdryConstW_tw m hm Cexp + (m : ℝ) * |α| * capMassConstW_tw m Cexp
              + Cexp * (Cap.hemisphere m).K)) * R := by
  set C : Cap m := Cap.hemisphere m with hCdef
  have hgrad := cap_upper_gradient_tw C hR hexp
  have hgrad0 : (0:ℝ) ≤ ∫ p in C.body, ‖(capLiftW_tw C hR gs.psi).gz p‖ ^ 2 :=
    setIntegral_nonneg (measurableSet_capBody C) fun _ _ => by positivity
  have hgradR : R⁻¹ * (∫ p in C.body, ‖(capLiftW_tw C hR gs.psi).gz p‖ ^ 2) ≤ C.K * Cexp ^ 2 * R := by
    have hstep : R⁻¹ * (∫ p in C.body, ‖(capLiftW_tw C hR gs.psi).gz p‖ ^ 2)
        ≤ R⁻¹ * (C.K * (Cexp ^ 2 * R ^ 2)) :=
      mul_le_mul_of_nonneg_left hgrad (by positivity)
    have hRR : R⁻¹ * R ^ 2 = R := by
      rw [sq, ← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul]
    have heq : R⁻¹ * (C.K * (Cexp ^ 2 * R ^ 2)) = C.K * Cexp ^ 2 * R := by
      calc R⁻¹ * (C.K * (Cexp ^ 2 * R ^ 2)) = C.K * Cexp ^ 2 * (R⁻¹ * R ^ 2) := by ring
        _ = C.K * Cexp ^ 2 * R := by rw [hRR]
    linarith [hstep, heq.le, heq.ge]
  have hgradRnn : (0:ℝ) ≤ R⁻¹ * (∫ p in C.body, ‖(capLiftW_tw C hR gs.psi).gz p‖ ^ 2) :=
    mul_nonneg (by positivity) hgrad0
  have hJ := cap_upper_J_tw hm hR hR1 hexp
  have hsplit : capEnergyTermW_tw hm α hR gs - Cap.beta C α
      = R⁻¹ * (∫ p in C.body, ‖(capLiftW_tw C hR gs.psi).gz p‖ ^ 2)
        + (capJFormW_tw hm α hR gs.psi
            - (R * gs.nu - (m : ℝ) * α) * massP (capLiftW_tw C hR gs.psi) - Cap.beta C α) := by
    rw [capEnergyTermW_tw]; ring
  rw [hsplit]
  calc |R⁻¹ * (∫ p in C.body, ‖(capLiftW_tw C hR gs.psi).gz p‖ ^ 2)
        + (capJFormW_tw hm α hR gs.psi
            - (R * gs.nu - (m : ℝ) * α) * massP (capLiftW_tw C hR gs.psi) - Cap.beta C α)|
      ≤ |R⁻¹ * (∫ p in C.body, ‖(capLiftW_tw C hR gs.psi).gz p‖ ^ 2)|
        + |capJFormW_tw hm α hR gs.psi
            - (R * gs.nu - (m : ℝ) * α) * massP (capLiftW_tw C hR gs.psi) - Cap.beta C α| :=
        abs_add_le _ _
    _ ≤ C.K * Cexp ^ 2 * R
        + (|α| * capBdryConstW_tw m hm Cexp + (m : ℝ) * |α| * capMassConstW_tw m Cexp
            + Cexp * C.K) * R := by
        rw [abs_of_nonneg hgradRnn]
        linarith [hgradR, hJ]
    _ = (C.K * Cexp ^ 2
          + (|α| * capBdryConstW_tw m hm Cexp + (m : ℝ) * |α| * capMassConstW_tw m Cexp
              + Cexp * C.K)) * R := by ring


end
end RobinCaps.ThinDomain
