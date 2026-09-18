import RobinCaps.Cap.SliceAC
import RobinCaps.ThinDomain.BulkMass
import RobinCaps.ThinDomain.TrialBound
import RobinCaps.Compact.RayleighAlgebra

/-!
# `lem:cap` for weak-`H¹` functions on the unit cap, against an explicit interface

This file formalises the manuscript's

* `eq:cap-lower`  `E_cap[u] ≥ (β(𝒞) − CR)|p|² + (2R)⁻¹‖∇g‖²_{L²(𝒞)}`,
* `eq:cap-mass-bound`  `N_cap[u] ≤ CR|p|² + CR‖∇g‖²_{L²(𝒞)}`

(`reference/robin_endcaps_corrected_en.tex`, `lem:cap`, lines 601–645) for **weak** `H¹`
functions `U : H1P C.body` on the fixed unit cap `𝒞 = C.body`, together with the weighted
Poincaré inequality `lem:weighted-P` that its proof quotes.

`RobinCaps/Cap/EnergyC1.lean` proves the same statements for globally `C¹` trial functions; the
present file is the weak-function counterpart.  Two analytic ingredients are **not** available in
mathlib `v4.26.0` and are therefore stated here as an explicit interface, to be discharged
elsewhere:

* `CapTraceData C` — the trace operator on the exposed boundary `Γ` of the unit cap, bundled
  exactly like `RobinCaps.ThinDomain.TraceData` of `RobinCaps/ThinDomain/Boundary.lean`
  (boundary representative, induced bilinear form, consistency on functions continuous up to the
  boundary, and the trace inequality);
* `CapEntranceL2 C C₁` — square integrability of the entrance trace `Tr_Σ U` on the entrance disk
  `Σ = {-K} × B_m(1)` together with the trace bound `‖Tr_Σ U‖²_{L²(Σ)} ≤ C₁(‖U‖² + ‖∇U‖²)`.
  For the cap component of a thin-domain function this is supplied by the interface trace through
  the bulk (`RobinCaps/ThinDomain/InterfaceTrace.lean`); for the cap alone it is a trace theorem;
* `CapPoincare C CP` — the Poincaré–Wirtinger inequality on the fixed cap: every `U ∈ H¹(𝒞)` has
  a constant `t` with `‖U − t‖²_{L²(𝒞)} ≤ CP‖∇U‖²_{L²(𝒞)}`.  This is the "Poincaré inequality on
  the fixed domain" invoked in the first line of the manuscript's proof of `lem:weighted-P`.

**Everything else is proved**: the weighted Poincaré inequality `weighted_poincare_lw`
(`lem:weighted-P`), the expansion of `J` and of the mass along `U = g + c·1`, and the two
conclusions `cap_lower_weak` / `cap_mass_bound_weak`, whose scalar core is re-used verbatim from
`RobinCaps.Cap.cap_lower_expand` and `RobinCaps.Transverse.cap_lower_algebra`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Filter Metric
open scoped ContDiff ENNReal Topology

namespace RobinCaps
namespace Cap

open RobinCaps.ThinDomain RobinCaps.Sobolev

noncomputable section

variable {m : ℕ}

/-! ## 1. Constant elements of `H1P C.body` -/

/-- The constant function `t` as an element of `H¹(𝒞)`, with vanishing weak gradient. -/
def constP (C : Cap m) (t : ℝ) : H1P C.body where
  toFun := fun _ => t
  gx := fun _ => 0
  gz := fun _ => 0
  memL2 := memLp_const t
  gx_memL2 := memLp_const 0
  gz_memL2 := memLp_const 0
  hasWeakGrad := by
    have h := hasWeakGradP_classical C.body (fun _ : CapSpace m => t) contDiff_const
    have h1 : dxP (fun _ : CapSpace m => t) = fun _ => (0 : ℝ) := by
      funext p; simp [dxP]
    have h2 : gradZP (fun _ : CapSpace m => t) = fun _ => (0 : EuclideanSpace ℝ (Fin m)) := by
      funext p
      ext i
      simp [gradZP]
    rwa [h1, h2] at h

@[simp] theorem constP_toFun (C : Cap m) (t : ℝ) : (constP C t).toFun = fun _ => t := rfl
@[simp] theorem constP_gx (C : Cap m) (t : ℝ) : (constP C t).gx = fun _ => (0 : ℝ) := rfl
@[simp] theorem constP_gz (C : Cap m) (t : ℝ) :
    (constP C t).gz = fun _ => (0 : EuclideanSpace ℝ (Fin m)) := rfl

/-- The constant function `1` as an element of `H¹(𝒞)`. -/
def oneP (C : Cap m) : H1P C.body := constP C 1

@[simp] theorem oneP_toFun (C : Cap m) : (oneP C).toFun = fun _ => (1 : ℝ) := rfl

theorem constP_eq_smul (C : Cap m) (t : ℝ) : constP C t = t • oneP C := by
  refine H1P.ext ?_ ?_ ?_
  · funext p; simp [oneP]
  · funext p; simp [oneP]
  · funext p; simp [oneP]

/-- `‖t‖²_{L²(𝒞)} = t²|𝒞|`. -/
theorem massP_constP (C : Cap m) (t : ℝ) :
    massP (constP C t) = t ^ 2 * C.revolutionVolume := by
  rw [massP]
  simp only [constP_toFun]
  rw [setIntegral_const, smul_eq_mul, measureReal_def, volume_body_eq_of_cap m C]
  ring

/-- `|𝒞| ≥ 0`. -/
theorem revolutionVolume_nonneg_lw (C : Cap m) : 0 ≤ C.revolutionVolume := by
  rw [← volume_body_eq_of_cap m C]
  exact ENNReal.toReal_nonneg

/-- A constant has vanishing Dirichlet energy. -/
@[simp] theorem dirichletP_constP (C : Cap m) (t : ℝ) : dirichletP (constP C t) = 0 := by
  rw [dirichletP]
  simp

theorem subP_gx_lw {Ω : Set (CapSpace m)} (u v : H1P Ω) :
    (u - v).gx = fun p => u.gx p - v.gx p := by
  have h : u - v = u + (-1 : ℝ) • v := by rw [neg_one_smul, ← sub_eq_add_neg]
  rw [h]; funext p
  simp only [H1P.add_gx, H1P.smul_gx, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem subP_gz_lw {Ω : Set (CapSpace m)} (u v : H1P Ω) :
    (u - v).gz = fun p => u.gz p - v.gz p := by
  have h : u - v = u + (-1 : ℝ) • v := by rw [neg_one_smul, ← sub_eq_add_neg]
  rw [h, H1P.add_gz, H1P.smul_gz]
  funext p
  simp only [Pi.add_apply, neg_smul, one_smul, Pi.neg_apply]
  abel

/-- Subtracting a constant does not change the weak gradient, hence not the Dirichlet energy. -/
theorem dirichletP_sub_constP (C : Cap m) (u : H1P C.body) (t : ℝ) :
    dirichletP (u - constP C t) = dirichletP u := by
  rw [dirichletP, dirichletP]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  rw [subP_gx_lw, subP_gz_lw]
  simp

/-- The pointwise description of `u − t`. -/
theorem sub_constP_toFun (C : Cap m) (u : H1P C.body) (t : ℝ) (p : CapSpace m) :
    (u - constP C t).toFun p = u.toFun p - t := by
  rw [H1P.sub_toFun]; simp

/-! ## 2. The interface

The three structures of this section are exactly the analytic inputs that mathlib `v4.26.0`
does not provide and that the manuscript's proof of `lem:cap` uses.  Everything after this
section is proved from them. -/

/-- The **`Γ`-pairing of the unit cap**: the polarised form of `RobinCaps.Cap.capBoundary`,
i.e. `∫_Γ f g dℋ^m` written in the revolution parametrisation as the lateral piece
(`RobinCaps.ThinDomain.capLateralIntegral`) plus the terminal disk of radius `θ(0)`. -/
def capGammaPair (C : Cap m) (f g : CapSpace m → ℝ) : ℝ :=
  ThinDomain.capLateralIntegral C (fun p => f p * g p)
    + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0), f (0, z) * g (0, z)

/-- On the diagonal the `Γ`-pairing is the exposed-boundary energy `∫_Γ |f|² dℋ^m` of
`RobinCaps/Cap/EnergyC1.lean`. -/
theorem capGammaPair_self (C : Cap m) (f : CapSpace m → ℝ) :
    capGammaPair C f f = capBoundary C f := by
  rw [capGammaPair, capBoundary]
  congr 1
  · congr 1; funext p; rw [sq]
  · exact integral_congr_ae (Eventually.of_forall fun z => (sq (f (0, z))).symm)

/-- **Interface 1: the trace on the exposed boundary `Γ` of the unit cap.**

Mathlib `v4.26.0` has no trace operator (no surface measure, no Sobolev extension), so — exactly
as in `RobinCaps.ThinDomain.TraceData` for the thin domain — the trace of a weak `H¹` function on
`Γ` is taken as *data*, and the whole cap lemma is stated for a given `CapTraceData`.

The fields are:

* `trΓ u` — a **boundary representative** of `u`, a pointwise function on `CapSpace m` whose
  values on the revolution parametrisation of `Γ` are the boundary values of `u`;
* `trΓ_add`, `trΓ_smul` — linearity of the representative;
* `bdΓ` — the induced **boundary bilinear form**, bundled as a genuine `ℝ`-bilinear map;
* `bdΓ_eq` — `bdΓ u v` **is** the concrete revolution boundary integral `∫_Γ (Tr u)(Tr v) dℋ^m`
  of `capGammaPair`, which links the analytic assumption to the explicit cap geometry;
* `bdΓ_symm`, `bdΓ_nonneg` — symmetry and nonnegativity of the boundary form;
* `trΓ_continuous` — **consistency**: on functions continuous up to the boundary the trace is
  the restriction, so that the boundary energy is the honest `∫_Γ u² dℋ^m` of
  `RobinCaps.Cap.capBoundary`.  This is what pins `J[1] = ω_m β(𝒞)` (`capJW_oneP`);
* `traceConst`, `traceConst_nonneg`, `trace_ineq` — the **trace inequality on `Γ`**
  `∫_Γ |Tr u|² dℋ^m ≤ C₀ (‖∇u‖²_{L²(𝒞)} + ‖u‖²_{L²(𝒞)})`;
* `vanishes_ae` — the trace kills elements whose representative vanishes a.e. on `𝒞`, so the
  boundary form descends to the a.e. quotient.

**Nothing in this file constructs a `CapTraceData`.** -/
structure CapTraceData (C : Cap m) where
  /-- The boundary representative on `Γ` of an `H¹(𝒞)` element. -/
  trΓ : H1P C.body → (CapSpace m → ℝ)
  /-- The representative is additive. -/
  trΓ_add : ∀ u v, trΓ (u + v) = trΓ u + trΓ v
  /-- The representative is homogeneous. -/
  trΓ_smul : ∀ (c : ℝ) (u), trΓ (c • u) = c • trΓ u
  /-- The boundary bilinear form `(u,v) ↦ ∫_Γ (Tr u)(Tr v) dℋ^m`. -/
  bdΓ : H1P C.body →ₗ[ℝ] H1P C.body →ₗ[ℝ] ℝ
  /-- The bilinear form is the concrete revolution boundary integral of the representatives. -/
  bdΓ_eq : ∀ u v, bdΓ u v = capGammaPair C (trΓ u) (trΓ v)
  /-- The boundary form is symmetric. -/
  bdΓ_symm : ∀ u v, bdΓ u v = bdΓ v u
  /-- The boundary form is nonnegative on the diagonal. -/
  bdΓ_nonneg : ∀ u, 0 ≤ bdΓ u u
  /-- On functions continuous up to the boundary the trace is the restriction. -/
  trΓ_continuous : ∀ u : H1P C.body, ContinuousOn u.toFun (closure C.body) →
    bdΓ u u = capBoundary C u.toFun
  /-- The constant of the trace inequality on `Γ`. -/
  traceConst : ℝ
  /-- The constant of the trace inequality is nonnegative. -/
  traceConst_nonneg : 0 ≤ traceConst
  /-- **The trace inequality on `Γ`**: `∫_Γ |Tr u|² ≤ C₀ (‖∇u‖² + ‖u‖²)`. -/
  trace_ineq : ∀ u, bdΓ u u ≤ traceConst * (dirichletP u + massP u)
  /-- The boundary form only sees the a.e. class of the representative. -/
  vanishes_ae : ∀ u, u.toFun =ᵐ[volume.restrict C.body] 0 → ∀ v, bdΓ u v = 0

/-- **Interface 2: the entrance trace is in `L²(Σ)`, with the trace bound.**

`RobinCaps.Cap.entranceVal` (`RobinCaps/Cap/SliceAC.lean`) already *constructs*, for every
`u ∈ H¹(𝒞)`, a measurable entrance value `Tr_Σ u : B_m(1) → ℝ` characterised by
`entranceVal_spec`.  What is missing — and what a trace theorem would give — is that this
function is square integrable on the entrance disk with the quantitative bound

`‖Tr_Σ u‖²_{L²(B_m(1))} ≤ C₁ (‖u‖²_{L²(𝒞)} + ‖∇u‖²_{L²(𝒞)})`.

For the cap component of a thin-domain function this bound is supplied by the interface trace
through the bulk (`RobinCaps/ThinDomain/InterfaceTrace.lean`, in progress); for the cap alone
it *is* a trace theorem on `Σ`, which mathlib does not have. -/
structure CapEntranceL2 (C : Cap m) (C₁ : ℝ) : Prop where
  /-- The constant is nonnegative. -/
  nonneg : 0 ≤ C₁
  /-- The entrance trace is square integrable on the entrance disk. -/
  memL2 : ∀ u : H1P C.body,
    MemLp (entranceVal C u) 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1))
  /-- The `L²(Σ)` trace bound. -/
  bound : ∀ u : H1P C.body,
    (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, entranceVal C u z ^ 2)
      ≤ C₁ * (massP u + dirichletP u)

/-- **Interface 3: the Poincaré–Wirtinger inequality on the fixed cap.**

This is the "Poincaré inequality on the fixed domain `𝒞`" quoted in the first line of the
manuscript's proof of `lem:weighted-P`: every `u ∈ H¹(𝒞)` is `L²`-close to a constant at the
scale of its gradient.  Stated with an unspecified constant `t` (rather than the mean value
`|𝒞|⁻¹∫_𝒞 u`) so that no nondegeneracy of `𝒞` has to be assumed. -/
structure CapPoincare (C : Cap m) (CP : ℝ) : Prop where
  /-- The constant is nonnegative. -/
  nonneg : 0 ≤ CP
  /-- `‖u − t‖²_{L²(𝒞)} ≤ CP ‖∇u‖²_{L²(𝒞)}` for some real `t`. -/
  bound : ∀ u : H1P C.body, ∃ t : ℝ, massP (u - constP C t) ≤ CP * dirichletP u

/-! ## 3. The weak cap functionals -/

/-- **`eq:J-definition` for weak functions**: `J[U] = α ∫_Γ |Tr U|² dℋ^m − mα ∫_𝒞 |U|²`. -/
def capJW (C : Cap m) (α : ℝ) (td : CapTraceData C) (u : H1P C.body) : ℝ :=
  α * td.bdΓ u u - (m : ℝ) * α * massP u

/-- The sesquilinear (here: bilinear) form `B_J` associated with `capJW`. -/
def capJBilinW (C : Cap m) (α : ℝ) (td : CapTraceData C) (u v : H1P C.body) : ℝ :=
  α * td.bdΓ u v - (m : ℝ) * α * massBilinP u v

/-- **`eq:exact-cap-energy` for weak functions**:
`E_cap[u] = R⁻¹‖∇U‖²_{L²(𝒞)} + J[U] − δ_R‖U‖²_{L²(𝒞)}`. -/
def capEnergyW (C : Cap m) (α : ℝ) (td : CapTraceData C) (R δ : ℝ) (u : H1P C.body) : ℝ :=
  R⁻¹ * dirichletP u + capJW C α td u - δ * massP u

/-- **`eq:exact-cap-mass` for weak functions**: `N_cap[u] = R‖U‖²_{L²(𝒞)}`. -/
def capMassScaledW (R : ℝ) {C : Cap m} (u : H1P C.body) : ℝ := R * massP u

/-! ## 4. The decomposition `U = g + c` of `eq:c-g-definition` -/

/-- `p = ⟨Tr_Σ U, Ψ_R⟩_{L²(Σ)}`, the entrance trace paired with the transverse ground state. -/
def pCoefW (C : Cap m) (ψ : EuclideanSpace ℝ (Fin m) → ℝ) (u : H1P C.body) : ℝ :=
  ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, entranceVal C u z * ψ z

/-- `c = p / d_R`. -/
def cCoefW (C : Cap m) (ψ : EuclideanSpace ℝ (Fin m) → ℝ) (dR : ℝ) (u : H1P C.body) : ℝ :=
  pCoefW C ψ u / dR

/-- `g = U − c`. -/
def gPartW (C : Cap m) (ψ : EuclideanSpace ℝ (Fin m) → ℝ) (dR : ℝ) (u : H1P C.body) :
    H1P C.body :=
  u - constP C (cCoefW C ψ dR u)

theorem gPartW_add_const (C : Cap m) (ψ : EuclideanSpace ℝ (Fin m) → ℝ) (dR : ℝ)
    (u : H1P C.body) :
    gPartW C ψ dR u + cCoefW C ψ dR u • oneP C = u := by
  rw [gPartW, ← constP_eq_smul, sub_add_cancel]

/-- `∇g = ∇U` (`lem:cap`, first line of the proof). -/
theorem dirichletP_gPartW (C : Cap m) (ψ : EuclideanSpace ℝ (Fin m) → ℝ) (dR : ℝ)
    (u : H1P C.body) : dirichletP (gPartW C ψ dR u) = dirichletP u :=
  dirichletP_sub_constP C u _

/-! ## 5. `lem:weighted-P`: the Poincaré inequality with a weighted entrance constraint -/

instance isFiniteMeasure_restrict_unitBall_lw (m : ℕ) :
    IsFiniteMeasure (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩

/-- **The entrance trace of `u − t` is `Tr_Σ u − t`.**

`entranceVal` is defined through a measurable representative of `u`, so it is not *pointwise*
linear; the identity is recovered a.e. from the uniqueness built into `entranceVal_spec`. -/
theorem entranceVal_sub_constP (C : Cap m) (u : H1P C.body) (t : ℝ) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)),
      entranceVal C (u - constP C t) z = entranceVal C u z - t := by
  have hgx : ∀ p : CapSpace m, (u - constP C t).gx p = u.gx p := by
    intro p; rw [subP_gx_lw]; simp
  filter_upwards [entranceVal_spec C u, entranceVal_spec C (u - constP C t),
    ae_restrict_mem measurableSet_ball] with z hu hv hzb
  have hznorm : ‖z‖ < 1 := mem_ball_zero_iff.1 hzb
  have hKe : -C.K < exitTime C z := (exitTime_mem C hznorm).1
  have hpos : (0 : ℝ≥0∞) < volume (Ioo (-C.K) (exitTime C z)) := by
    rw [Real.volume_Ioo, ENNReal.ofReal_pos]; linarith
  haveI : (ae (volume.restrict (Ioo (-C.K) (exitTime C z)))).NeBot := by
    refine ae_neBot.2 ?_
    rw [Ne, Measure.restrict_eq_zero]
    exact hpos.ne'
  obtain ⟨s, hs1, hs2⟩ := (hu.and hv).exists
  have hint : (∫ r in (-C.K)..s, (u - constP C t).gx (r, z))
      = ∫ r in (-C.K)..s, u.gx (r, z) := by
    refine intervalIntegral.integral_congr (fun r _ => ?_)
    exact hgx (r, z)
  rw [hint, sub_constP_toFun C u t (s, z), hs1] at hs2
  linarith

/-- `‖u‖² ≤ 2‖u − t‖² + 2t²|𝒞|`. -/
theorem massP_le_sub_constP (C : Cap m) (u : H1P C.body) (t : ℝ) :
    massP u ≤ 2 * massP (u - constP C t) + 2 * t ^ 2 * C.revolutionVolume := by
  have hbody := measurableSet_body' C
  have hMi : IntegrableOn (fun p : CapSpace m => u.toFun p ^ 2) C.body volume :=
    u.memL2.integrable_sq
  have hHi : IntegrableOn (fun p : CapSpace m => (u - constP C t).toFun p ^ 2) C.body volume :=
    (u - constP C t).memL2.integrable_sq
  have hCi : IntegrableOn (fun _ : CapSpace m => t ^ 2) C.body volume :=
    integrable_const (t ^ 2)
  have hsum : IntegrableOn
      (fun p : CapSpace m => 2 * (u - constP C t).toFun p ^ 2 + 2 * t ^ 2) C.body volume :=
    (hHi.const_mul 2).add (hCi.const_mul 2)
  have hptw : ∀ p ∈ C.body,
      u.toFun p ^ 2 ≤ 2 * (u - constP C t).toFun p ^ 2 + 2 * t ^ 2 := by
    intro p _
    rw [sub_constP_toFun C u t p]
    nlinarith [sq_nonneg (u.toFun p - 2 * t)]
  have hmain := setIntegral_mono_on hMi hsum hbody hptw
  rw [integral_add (hHi.const_mul 2) (hCi.const_mul 2), integral_const_mul, setIntegral_const,
    smul_eq_mul, measureReal_def, volume_body_eq_of_cap m C] at hmain
  rw [massP, massP]
  linarith [hmain]

/-- The constant of `lem:weighted-P`:
`‖g‖²_{L²(𝒞)} ≤ (2C_P + 8|𝒞|C₁(C_P+1)/ω_m) ‖∇g‖²_{L²(𝒞)}`. -/
def capPoincareConstW (C : Cap m) (CP C₁ : ℝ) : ℝ :=
  2 * CP + 8 * C.revolutionVolume * C₁ * (CP + 1) / omega m

theorem capPoincareConstW_nonneg (C : Cap m) {CP C₁ : ℝ} (hCP : 0 ≤ CP) (hC₁ : 0 ≤ C₁) :
    0 ≤ capPoincareConstW C CP C₁ := by
  have hV := revolutionVolume_nonneg_lw C
  have hω := omega_pos m
  refine add_nonneg (by linarith) (div_nonneg ?_ hω.le)
  have : (0 : ℝ) ≤ 8 * C.revolutionVolume * C₁ := by positivity
  nlinarith

/-- **`lem:weighted-P` (manuscript lines 575–599), weak form.**

If `g ∈ H¹(𝒞)` satisfies the weighted entrance constraint `⟨Tr_Σ g, Ψ_R⟩_{L²(Σ)} = 0`, then
`‖g‖²_{L²(𝒞)} ≤ C ‖∇g‖²_{L²(𝒞)}` with `C = capPoincareConstW C CP C₁` independent of `R`. -/
theorem weighted_poincare_lw (C : Cap m) {CP C₁ : ℝ} (hpo : CapPoincare C CP)
    (hen : CapEntranceL2 C C₁)
    {ψ : EuclideanSpace ℝ (Fin m) → ℝ}
    (hψ : MemLp ψ 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)))
    (hψ1 : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ψ z ^ 2) = 1)
    {dR : ℝ} (hdR : dR = ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ψ z)
    (hdRge : Real.sqrt (omega m) / 2 ≤ dR)
    (g : H1P C.body) (horth : pCoefW C ψ g = 0) :
    massP g ≤ capPoincareConstW C CP C₁ * dirichletP g := by
  classical
  set B : Set (EuclideanSpace ℝ (Fin m)) := ball (0 : EuclideanSpace ℝ (Fin m)) 1 with hB
  set D : ℝ := dirichletP g with hD
  have hD0 : 0 ≤ D := dirichletP_nonneg g
  have hω := omega_pos m
  have hV := revolutionVolume_nonneg_lw C
  -- the Poincaré constant `t`
  obtain ⟨t, ht⟩ := hpo.bound g
  set h : H1P C.body := g - constP C t with hh
  have hDh : dirichletP h = D := dirichletP_sub_constP C g t
  have hMh : massP h ≤ CP * D := ht
  have hMh0 : 0 ≤ massP h := massP_nonneg h
  -- the entrance bound for `h`
  have hEh : (∫ z in B, entranceVal C h z ^ 2) ≤ C₁ * (CP + 1) * D := by
    refine (hen.bound h).trans ?_
    rw [hDh]
    have : massP h + D ≤ (CP + 1) * D := by linarith
    calc C₁ * (massP h + D) ≤ C₁ * ((CP + 1) * D) :=
          mul_le_mul_of_nonneg_left this hen.nonneg
      _ = C₁ * (CP + 1) * D := by ring
  -- integrability
  have hψint : Integrable ψ (volume.restrict B) := hψ.integrable (by norm_num)
  have hψ2 : Integrable (fun z => ψ z ^ 2) (volume.restrict B) := by
    simpa [sq] using hψ.integrable_mul hψ
  have hgm := hen.memL2 g
  have hhm := hen.memL2 h
  have hgsq : Integrable (fun z => entranceVal C g z ^ 2) (volume.restrict B) := by
    simpa [sq] using hgm.integrable_mul hgm
  have hhsq : Integrable (fun z => entranceVal C h z ^ 2) (volume.restrict B) := by
    simpa [sq] using hhm.integrable_mul hhm
  have hgψ : Integrable (fun z => entranceVal C g z * ψ z) (volume.restrict B) :=
    hgm.integrable_mul hψ
  have hhψ : Integrable (fun z => entranceVal C h z * ψ z) (volume.restrict B) :=
    hhm.integrable_mul hψ
  -- the pairing of `Tr_Σ h` with `ψ` is `-t d_R`
  have hpair : (∫ z in B, entranceVal C h z * ψ z) = -(t * dR) := by
    have hae : (∫ z in B, entranceVal C h z * ψ z)
        = ∫ z in B, (entranceVal C g z * ψ z - t * ψ z) := by
      refine integral_congr_ae ?_
      filter_upwards [entranceVal_sub_constP C g t] with z hz
      rw [hh, hz]; ring
    rw [hae, integral_sub hgψ (hψint.const_mul t), integral_const_mul]
    rw [← hdR]
    have : (∫ z in B, entranceVal C g z * ψ z) = 0 := horth
    rw [this]; ring
  -- Cauchy–Schwarz against the normalised profile
  have hcs : (∫ z in B, entranceVal C h z * ψ z) ^ 2
      ≤ ∫ z in B, entranceVal C h z ^ 2 :=
    ThinDomain.sq_integral_mul_le_integral_sq hhsq hhψ hψ2 hψ1
  rw [hpair] at hcs
  -- hence `t²` is controlled
  have hdRpos : 0 < dR := by
    have : 0 < Real.sqrt (omega m) := Real.sqrt_pos.2 hω
    linarith
  have hdRsq : omega m / 4 ≤ dR ^ 2 := by
    have h1 : Real.sqrt (omega m) / 2 ≤ dR := hdRge
    have h2 : (Real.sqrt (omega m) / 2) ^ 2 ≤ dR ^ 2 := by
      apply sq_le_sq' _ h1
      have : 0 ≤ Real.sqrt (omega m) := Real.sqrt_nonneg _
      linarith
    have h3 : (Real.sqrt (omega m) / 2) ^ 2 = omega m / 4 := by
      rw [div_pow, Real.sq_sqrt hω.le]; norm_num
    linarith [h2, h3]
  have ht2 : t ^ 2 * (omega m / 4) ≤ C₁ * (CP + 1) * D := by
    have h1 : t ^ 2 * (omega m / 4) ≤ t ^ 2 * dR ^ 2 :=
      mul_le_mul_of_nonneg_left hdRsq (sq_nonneg t)
    have h2 : t ^ 2 * dR ^ 2 = (-(t * dR)) ^ 2 := by ring
    linarith [hcs, hEh, h1, h2.le, h2.ge]
  have ht2' : t ^ 2 ≤ 4 * (C₁ * (CP + 1) * D) / omega m := by
    rw [le_div_iff₀ hω]
    linarith [ht2]
  -- assembling
  have hfin := massP_le_sub_constP C g t
  rw [← hh] at hfin
  have hstep : 2 * t ^ 2 * C.revolutionVolume
      ≤ 2 * (4 * (C₁ * (CP + 1) * D) / omega m) * C.revolutionVolume := by
    have := mul_le_mul_of_nonneg_left ht2' (by norm_num : (0:ℝ) ≤ 2)
    exact mul_le_mul_of_nonneg_right this hV
  have hfinal : massP g ≤ 2 * (CP * D) + 2 * (4 * (C₁ * (CP + 1) * D) / omega m)
      * C.revolutionVolume := by
    linarith [hfin, hMh, hstep]
  refine hfinal.trans ?_
  rw [capPoincareConstW]
  have : 2 * (4 * (C₁ * (CP + 1) * D) / omega m) * C.revolutionVolume
      = 8 * C.revolutionVolume * C₁ * (CP + 1) / omega m * D := by
    field_simp; ring
  rw [this]
  ring_nf
  linarith

/-! ## 6. `J[1] = ω_m β(𝒞)` and the expansions along `U = g + c` -/

theorem abs_le_of_sq_le_sq_lw {x y : ℝ} (h : x ^ 2 ≤ y ^ 2) (hy : 0 ≤ y) : |x| ≤ y := by
  nlinarith [abs_nonneg x, sq_abs x]

theorem abs_sub_le_lw (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  simpa [sub_eq_add_neg, abs_neg] using abs_add_le x (-y)

theorem habs_two_lw : |(2 : ℝ)| = 2 := by norm_num

/-- The boundary form of the constant `1` is the exposed area `ℋ^m(Γ)`. -/
theorem bdΓ_oneP (C : Cap m) (hm : 1 ≤ m) (hθ0 : 0 ≤ C.θ 0) (td : CapTraceData C) :
    td.bdΓ (oneP C) (oneP C) = C.revolutionArea := by
  rw [td.trΓ_continuous (oneP C) continuousOn_const]
  exact capBoundary_one C hm hθ0

theorem revolutionArea_nonneg_lw (C : Cap m) (hm : 1 ≤ m) (hθ0 : 0 ≤ C.θ 0)
    (td : CapTraceData C) : 0 ≤ C.revolutionArea := by
  rw [← bdΓ_oneP C hm hθ0 td]; exact td.bdΓ_nonneg _

/-- `‖1‖²_{L²(𝒞)} = |𝒞|`. -/
theorem massP_oneP (C : Cap m) : massP (oneP C) = C.revolutionVolume := by
  rw [oneP, massP_constP]; ring

/-- **`J[1] = ω_m β(𝒞)`** (manuscript line 625), for the weak functional. -/
theorem capJW_oneP (C : Cap m) (hm : 1 ≤ m) (hθ0 : 0 ≤ C.θ 0) (α : ℝ) (td : CapTraceData C) :
    capJW C α td (oneP C) = omega m * C.beta α := by
  have h := capJ_one C hm hθ0 α
  rw [capJ, capBoundary_one C hm hθ0, capMass_one] at h
  rw [capJW, bdΓ_oneP C hm hθ0 td, massP_oneP]
  linarith [h]

/-- The binomial expansion of the mass along `U = g + c·1`. -/
theorem massP_add_smul_oneP (C : Cap m) (g : H1P C.body) (c : ℝ) :
    massP (g + c • oneP C)
      = massP g + 2 * c * massBilinP g (oneP C) + c ^ 2 * massP (oneP C) := by
  have hs : ∀ u v : H1P C.body, (massBilinPₗ u) v = (massBilinPₗ v) u :=
    fun u v => massBilinP_comm u v
  have h := RobinCaps.Compact.bilin_add_smul_smul (Q := massBilinPₗ) hs g (oneP C) c
  simpa only [massBilinPₗ_apply, massBilinP_self] using h

/-- The binomial expansion of `J` along `U = g + c·1`; the cross term is `2c B_J(g,1)`. -/
theorem capJW_add_smul_oneP (C : Cap m) (α : ℝ) (td : CapTraceData C) (g : H1P C.body)
    (c : ℝ) :
    capJW C α td (g + c • oneP C)
      = capJW C α td g + 2 * c * capJBilinW C α td g (oneP C)
        + c ^ 2 * capJW C α td (oneP C) := by
  have hb := RobinCaps.Compact.bilin_add_smul_smul (Q := td.bdΓ) td.bdΓ_symm g (oneP C) c
  rw [capJW, capJW, capJBilinW, capJW, hb, massP_add_smul_oneP]
  ring

/-! ## 7. The scalar core of `eq:cap-lower` for weak functions

This is `RobinCaps.Cap.cap_lower_c1` with the `C¹` functionals replaced by the weak ones; the
scalar work is done by `RobinCaps.Cap.cap_lower_expand` and
`RobinCaps.Transverse.cap_lower_algebra`, which are statements about real numbers only. -/

/-- **`eq:cap-lower`, algebraic core, weak version.** -/
theorem cap_lower_weak_core (C : Cap m) {α R δ : ℝ} (td : CapTraceData C)
    {U g : H1P C.body} {c G A : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (hA : 0 ≤ A) (hG0 : 0 ≤ G)
    (hgrad : dirichletP U = G ^ 2)
    (hJg : |capJW C α td g| ≤ A * G ^ 2)
    (hBJ : |capJW C α td U - capJW C α td g - c ^ 2 * capJW C α td (oneP C)| ≤ A * |c| * G)
    (hNc : |massP U - massP g - c ^ 2 * massP (oneP C)| ≤ A * |c| * G)
    (hLg : massP g ≤ A * G ^ 2) (hVol : massP (oneP C) ≤ A)
    (hδ : |δ| ≤ A * R)
    (hsmall : (A + A ^ 2) + (A + A ^ 2) * R ≤ 1 / (4 * R)) :
    G ^ 2 / (2 * R)
        + (capJW C α td (oneP C) - ((A + A ^ 2) + (A + A ^ 2) ^ 2) * R) * c ^ 2
      ≤ capEnergyW C α td R δ U := by
  have hc2 : (0 : ℝ) ≤ c ^ 2 := sq_nonneg _
  have hE : capEnergyW C α td R δ U
      = R⁻¹ * G ^ 2 + capJW C α td U - δ * massP U := by rw [capEnergyW, hgrad]
  have hJU : capJW C α td g + c ^ 2 * capJW C α td (oneP C) - A * |c| * G
      ≤ capJW C α td U := by
    have := (abs_le.1 hBJ).1
    linarith
  have hJgl : -(A * G ^ 2) ≤ capJW C α td g := (abs_le.1 hJg).1
  have hMU : massP U ≤ A * G ^ 2 + A * c ^ 2 + A * |c| * G := by
    have h1 := (abs_le.1 hNc).2
    have h2 : c ^ 2 * massP (oneP C) ≤ c ^ 2 * A := mul_le_mul_of_nonneg_left hVol hc2
    nlinarith [h1, h2, hLg]
  have hkey := cap_lower_expand (R := R) (A := A) (J1 := capJW C α td (oneP C))
    (JU := capJW C α td U) (Jg := capJW C α td g) (MU := massP U) (c := c) (G := G) (δ := δ)
    (E := capEnergyW C α td R δ U) hR hR1 hA hG0 hE hJgl hJU hMU (massP_nonneg U) hδ
  exact RobinCaps.Transverse.cap_lower_algebra hR hsmall hkey

/-! ## 8. The explicit constants -/

/-- `∫_Γ |Tr g|² ≤ (capGammaConstW) ‖∇g‖²` for `g` with vanishing weighted entrance trace:
the trace constant of `Γ` times `1 + ` the weighted Poincaré constant. -/
def capGammaConstW (C : Cap m) (td : CapTraceData C) (CP C₁ : ℝ) : ℝ :=
  td.traceConst * (1 + capPoincareConstW C CP C₁)

/-- **The constant `C` of `lem:cap`.**  It dominates each of the six quantities that the scalar
core `cap_lower_weak_core` needs (`capConstW_ge`). -/
def capConstW (C : Cap m) (α : ℝ) (td : CapTraceData C) (CP C₁ Cδ : ℝ) : ℝ :=
  α * capGammaConstW C td CP C₁ + (m : ℝ) * α * capPoincareConstW C CP C₁
    + 2 * (α * Real.sqrt (capGammaConstW C td CP C₁ * C.revolutionArea)
        + (m : ℝ) * α * Real.sqrt (capPoincareConstW C CP C₁ * C.revolutionVolume))
    + 2 * Real.sqrt (capPoincareConstW C CP C₁ * C.revolutionVolume)
    + capPoincareConstW C CP C₁ + C.revolutionVolume + Cδ

/-- The constant `C'` of `eq:cap-lower` in the `c`-variable. -/
def capLowerConstW (C : Cap m) (α : ℝ) (td : CapTraceData C) (CP C₁ Cδ : ℝ) : ℝ :=
  (capConstW C α td CP C₁ Cδ + capConstW C α td CP C₁ Cδ ^ 2)
    + (capConstW C α td CP C₁ Cδ + capConstW C α td CP C₁ Cδ ^ 2) ^ 2

/-- The explicit threshold `R₀` of `lem:cap`. -/
def capR0W (C : Cap m) (α : ℝ) (td : CapTraceData C) (CP C₁ Cδ : ℝ) : ℝ :=
  min 1 (8 * (capConstW C α td CP C₁ Cδ + capConstW C α td CP C₁ Cδ ^ 2) + 1)⁻¹

theorem capConstW_ge (C : Cap m) {α : ℝ} (hα : 0 ≤ α) (td : CapTraceData C)
    {CP C₁ Cδ : ℝ} (hCP : 0 ≤ CP) (hC₁ : 0 ≤ C₁) (hCδ : 0 ≤ Cδ) :
    0 ≤ capConstW C α td CP C₁ Cδ
      ∧ α * capGammaConstW C td CP C₁ + (m : ℝ) * α * capPoincareConstW C CP C₁
          ≤ capConstW C α td CP C₁ Cδ
      ∧ 2 * (α * Real.sqrt (capGammaConstW C td CP C₁ * C.revolutionArea)
          + (m : ℝ) * α * Real.sqrt (capPoincareConstW C CP C₁ * C.revolutionVolume))
          ≤ capConstW C α td CP C₁ Cδ
      ∧ 2 * Real.sqrt (capPoincareConstW C CP C₁ * C.revolutionVolume)
          ≤ capConstW C α td CP C₁ Cδ
      ∧ capPoincareConstW C CP C₁ ≤ capConstW C α td CP C₁ Cδ
      ∧ C.revolutionVolume ≤ capConstW C α td CP C₁ Cδ
      ∧ Cδ ≤ capConstW C α td CP C₁ Cδ := by
  have hP := capPoincareConstW_nonneg C hCP hC₁
  have hV := revolutionVolume_nonneg_lw C
  have hS : 0 ≤ capGammaConstW C td CP C₁ :=
    mul_nonneg td.traceConst_nonneg (by linarith)
  have h1 : 0 ≤ α * capGammaConstW C td CP C₁ := mul_nonneg hα hS
  have h2 : 0 ≤ (m : ℝ) * α * capPoincareConstW C CP C₁ :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg m) hα) hP
  have h3 : 0 ≤ 2 * (α * Real.sqrt (capGammaConstW C td CP C₁ * C.revolutionArea)
      + (m : ℝ) * α * Real.sqrt (capPoincareConstW C CP C₁ * C.revolutionVolume)) := by
    have a1 : 0 ≤ α * Real.sqrt (capGammaConstW C td CP C₁ * C.revolutionArea) :=
      mul_nonneg hα (Real.sqrt_nonneg _)
    have a2 : 0 ≤ (m : ℝ) * α
        * Real.sqrt (capPoincareConstW C CP C₁ * C.revolutionVolume) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg m) hα) (Real.sqrt_nonneg _)
    linarith
  have h4 : 0 ≤ 2 * Real.sqrt (capPoincareConstW C CP C₁ * C.revolutionVolume) := by
    have := Real.sqrt_nonneg (capPoincareConstW C CP C₁ * C.revolutionVolume)
    linarith
  rw [capConstW]
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith⟩

theorem capR0W_pos (C : Cap m) {α : ℝ} (hα : 0 ≤ α) (td : CapTraceData C)
    {CP C₁ Cδ : ℝ} (hCP : 0 ≤ CP) (hC₁ : 0 ≤ C₁) (hCδ : 0 ≤ Cδ) :
    0 < capR0W C α td CP C₁ Cδ := by
  have hA := (capConstW_ge C hα td hCP hC₁ hCδ).1
  rw [capR0W]
  refine lt_min one_pos (inv_pos.2 ?_)
  nlinarith [hA, sq_nonneg (capConstW C α td CP C₁ Cδ)]

/-- The smallness of `R` used by `cap_lower_weak_core`, from `R < R₀`. -/
theorem smallness_of_lt_lw {A R : ℝ} (hA : 0 ≤ A) (hR : 0 < R)
    (hlt : R < min 1 (8 * (A + A ^ 2) + 1)⁻¹) :
    R ≤ 1 ∧ (A + A ^ 2) + (A + A ^ 2) * R ≤ 1 / (4 * R) := by
  have hA1 : 0 ≤ A + A ^ 2 := by nlinarith [sq_nonneg A]
  have h1 : R ≤ 1 := (lt_of_lt_of_le hlt (min_le_left _ _)).le
  have h2 : R < (8 * (A + A ^ 2) + 1)⁻¹ := lt_of_lt_of_le hlt (min_le_right _ _)
  have hden : (0 : ℝ) < 8 * (A + A ^ 2) + 1 := by linarith
  have h3 : R * (8 * (A + A ^ 2) + 1) < 1 := by
    have := mul_lt_mul_of_pos_right h2 hden
    rwa [inv_mul_cancel₀ hden.ne'] at this
  refine ⟨h1, ?_⟩
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < 4 * R)]
  nlinarith [h3, hA1, h1, hR, mul_nonneg hA1 hR.le]

/-! ## 9. The entrance pairing of `g = U − c` -/

theorem pCoefW_sub_constP (C : Cap m) {C₁ : ℝ} (hen : CapEntranceL2 C C₁)
    {ψ : EuclideanSpace ℝ (Fin m) → ℝ}
    (hψ : MemLp ψ 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)))
    (u : H1P C.body) (t : ℝ) :
    pCoefW C ψ (u - constP C t)
      = pCoefW C ψ u - t * ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ψ z := by
  have hψint : Integrable ψ (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)) :=
    hψ.integrable (by norm_num)
  have hgψ : Integrable (fun z => entranceVal C u z * ψ z)
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)) :=
    (hen.memL2 u).integrable_mul hψ
  have hstep : pCoefW C ψ (u - constP C t)
      = ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
          (entranceVal C u z * ψ z - t * ψ z) := by
    refine integral_congr_ae ?_
    filter_upwards [entranceVal_sub_constP C u t] with z hz
    rw [hz]; ring
  rw [hstep, integral_sub hgψ (hψint.const_mul t), integral_const_mul]
  rfl

/-- **The entrance constraint of `eq:c-g-definition`**: `⟨Tr_Σ g, Ψ_R⟩ = 0`. -/
theorem pCoefW_gPartW (C : Cap m) {C₁ : ℝ} (hen : CapEntranceL2 C C₁)
    {ψ : EuclideanSpace ℝ (Fin m) → ℝ}
    (hψ : MemLp ψ 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)))
    {dR : ℝ} (hdR : dR = ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ψ z) (hdR0 : dR ≠ 0)
    (u : H1P C.body) : pCoefW C ψ (gPartW C ψ dR u) = 0 := by
  rw [gPartW, pCoefW_sub_constP C hen hψ, ← hdR, cCoefW]
  field_simp
  ring

/-- `d_R² ≤ ω_m`, by Cauchy–Schwarz against the normalised profile. -/
theorem dR_sq_le_omega_lw {m : ℕ} {ψ : EuclideanSpace ℝ (Fin m) → ℝ}
    (hψ : MemLp ψ 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)))
    (hψ1 : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ψ z ^ 2) = 1) :
    (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ψ z) ^ 2 ≤ omega m := by
  have hψint : Integrable ψ (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)) :=
    hψ.integrable (by norm_num)
  have hψ2 : Integrable (fun z => ψ z ^ 2)
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)) := by
    simpa [sq] using hψ.integrable_mul hψ
  have h1 : Integrable (fun _ : EuclideanSpace ℝ (Fin m) => (1 : ℝ) ^ 2)
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)) := integrable_const _
  have h2 : Integrable (fun z : EuclideanSpace ℝ (Fin m) => (1 : ℝ) * ψ z)
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)) := by
    simpa using hψint
  have hcs := ThinDomain.sq_integral_mul_le_integral_sq h1 h2 hψ2 hψ1
  have hone : (∫ _z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, (1 : ℝ) ^ 2) = omega m := by
    simp only [one_pow]
    rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def, omega]
  have hmul : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, (1 : ℝ) * ψ z)
      = ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ψ z := by
    simp
  rw [hone, hmul] at hcs
  exact hcs

/-! ## 10. `lem:cap` for weak functions -/

/-- **`eq:cap-lower` (`lem:cap`) for weak `H¹` functions, in the variable `c = p/d_R`.**

For every `U ∈ H¹(𝒞)`, with `p = ⟨Tr_Σ U, Ψ_R⟩`, `c = p/d_R` and `g = U − c`:

`E_cap[u] ≥ (2R)⁻¹‖∇g‖²_{L²(𝒞)} + (ω_m β(𝒞) − C'R) c²`  for `0 < R < R₀`,

with the explicit constant `C' = capLowerConstW` and the explicit threshold
`R₀ = capR0W`. -/
theorem cap_lower_weak (C : Cap m) (hm : 1 ≤ m) (hθ0 : 0 ≤ C.θ 0) (td : CapTraceData C)
    {CP C₁ Cδ α : ℝ} (hpo : CapPoincare C CP) (hen : CapEntranceL2 C C₁)
    (hCδ : 0 ≤ Cδ) (hα : 0 ≤ α)
    {ψ : EuclideanSpace ℝ (Fin m) → ℝ}
    (hψ : MemLp ψ 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)))
    (hψ1 : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ψ z ^ 2) = 1)
    {dR : ℝ} (hdR : dR = ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ψ z)
    (hdRge : Real.sqrt (omega m) / 2 ≤ dR)
    {R δ : ℝ} (hR : 0 < R) (hR0 : R < capR0W C α td CP C₁ Cδ) (hδ : |δ| ≤ Cδ * R)
    (U : H1P C.body) :
    dirichletP (gPartW C ψ dR U) / (2 * R)
        + (omega m * C.beta α - capLowerConstW C α td CP C₁ Cδ * R) * cCoefW C ψ dR U ^ 2
      ≤ capEnergyW C α td R δ U := by
  classical
  obtain ⟨hA0, hAe1, hAe2, hAe3, hAe4, hAe5, hAe6⟩ :=
    capConstW_ge C hα td hpo.nonneg hen.nonneg hCδ
  set A := capConstW C α td CP C₁ Cδ with hAdef
  set P := capPoincareConstW C CP C₁ with hPdef
  set S := capGammaConstW C td CP C₁ with hSdef
  have hP0 : 0 ≤ P := capPoincareConstW_nonneg C hpo.nonneg hen.nonneg
  have hV0 : 0 ≤ C.revolutionVolume := revolutionVolume_nonneg_lw C
  have hQ0 : 0 ≤ C.revolutionArea := revolutionArea_nonneg_lw C hm hθ0 td
  have hS0 : 0 ≤ S := mul_nonneg td.traceConst_nonneg (by linarith)
  have hω := omega_pos m
  have hdRpos : 0 < dR := by
    have : 0 < Real.sqrt (omega m) := Real.sqrt_pos.2 hω
    linarith
  -- the decomposition
  set c := cCoefW C ψ dR U with hcdef
  set g := gPartW C ψ dR U with hgdef
  set G := Real.sqrt (dirichletP U) with hGdef
  have hG0 : 0 ≤ G := Real.sqrt_nonneg _
  have hGsq : G ^ 2 = dirichletP U := Real.sq_sqrt (dirichletP_nonneg U)
  have hgrad : dirichletP U = G ^ 2 := hGsq.symm
  have hDg : dirichletP g = G ^ 2 := by rw [hgdef, dirichletP_gPartW, hGsq]
  have hU : g + c • oneP C = U := gPartW_add_const C ψ dR U
  have hG2 : (0 : ℝ) ≤ G ^ 2 := sq_nonneg _
  have hcG : (0 : ℝ) ≤ |c| * G := mul_nonneg (abs_nonneg _) hG0
  -- the weighted Poincaré inequality
  have horth : pCoefW C ψ g = 0 := pCoefW_gPartW C hen hψ hdR hdRpos.ne' U
  have hLgP : massP g ≤ P * G ^ 2 := by
    have := weighted_poincare_lw C hpo hen hψ hψ1 hdR hdRge g horth
    rw [hDg] at this
    exact this
  have hMg0 : 0 ≤ massP g := massP_nonneg g
  -- the boundary energy of `g`
  have hbg0 : 0 ≤ td.bdΓ g g := td.bdΓ_nonneg g
  have hbgS : td.bdΓ g g ≤ S * G ^ 2 := by
    have h := td.trace_ineq g
    have h2 : dirichletP g + massP g ≤ (1 + P) * G ^ 2 := by rw [hDg]; linarith [hLgP]
    have h3 : td.traceConst * (dirichletP g + massP g)
        ≤ td.traceConst * ((1 + P) * G ^ 2) :=
      mul_le_mul_of_nonneg_left h2 td.traceConst_nonneg
    have h4 : td.traceConst * ((1 + P) * G ^ 2) = S * G ^ 2 := by
      rw [hSdef, capGammaConstW, hPdef]; ring
    linarith [h, h3, h4.le, h4.ge]
  -- `|J[g]| ≤ A G²`
  have hSA : (0 : ℝ) ≤ α * S := mul_nonneg hα hS0
  have hPA : (0 : ℝ) ≤ (m : ℝ) * α * P :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg m) hα) hP0
  have hJg : |capJW C α td g| ≤ A * G ^ 2 := by
    have hup : capJW C α td g ≤ α * S * G ^ 2 := by
      have h1 : α * td.bdΓ g g ≤ α * (S * G ^ 2) := mul_le_mul_of_nonneg_left hbgS hα
      have h2 : (0 : ℝ) ≤ (m : ℝ) * α * massP g :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg m) hα) hMg0
      rw [capJW]; linarith [h1, h2]
    have hlo : -((m : ℝ) * α * P * G ^ 2) ≤ capJW C α td g := by
      have h1 : (0 : ℝ) ≤ α * td.bdΓ g g := mul_nonneg hα hbg0
      have h2 : (m : ℝ) * α * massP g ≤ (m : ℝ) * α * (P * G ^ 2) :=
        mul_le_mul_of_nonneg_left hLgP (mul_nonneg (Nat.cast_nonneg m) hα)
      rw [capJW]; linarith [h1, h2]
    have hu1 : α * S ≤ A := by linarith [hAe1]
    have hu2 : (m : ℝ) * α * P ≤ A := by linarith [hAe1]
    have hup2 : α * S * G ^ 2 ≤ A * G ^ 2 := mul_le_mul_of_nonneg_right hu1 hG2
    have hlo2 : (m : ℝ) * α * P * G ^ 2 ≤ A * G ^ 2 := mul_le_mul_of_nonneg_right hu2 hG2
    exact abs_le.2 ⟨by linarith, by linarith⟩
  -- Cauchy–Schwarz for the two bilinear forms
  have hcsb := RobinCaps.Compact.bilin_cauchy_schwarz (N := td.bdΓ) td.bdΓ_symm td.bdΓ_nonneg
    g (oneP C)
  rw [bdΓ_oneP C hm hθ0 td] at hcsb
  have hmsym : ∀ u v : H1P C.body, (massBilinPₗ u) v = (massBilinPₗ v) u :=
    fun u v => massBilinP_comm u v
  have hmnn : ∀ w : H1P C.body, 0 ≤ (massBilinPₗ w) w := by
    intro w; rw [massBilinPₗ_apply, massBilinP_self]; exact massP_nonneg w
  have hcsm := RobinCaps.Compact.bilin_cauchy_schwarz (N := massBilinPₗ) hmsym hmnn g (oneP C)
  simp only [massBilinPₗ_apply, massBilinP_self] at hcsm
  rw [massP_oneP] at hcsm
  -- the two cross-term bounds
  have hbdcross : |td.bdΓ g (oneP C)| ≤ Real.sqrt (S * C.revolutionArea) * G := by
    refine abs_le_of_sq_le_sq_lw ?_ (mul_nonneg (Real.sqrt_nonneg _) hG0)
    have hsq : (Real.sqrt (S * C.revolutionArea) * G) ^ 2 = S * C.revolutionArea * G ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (mul_nonneg hS0 hQ0)]
    rw [hsq]
    have hmono : td.bdΓ g g * C.revolutionArea ≤ S * G ^ 2 * C.revolutionArea :=
      mul_le_mul_of_nonneg_right hbgS hQ0
    linarith [hcsb, hmono]
  have hmcross : |massBilinP g (oneP C)| ≤ Real.sqrt (P * C.revolutionVolume) * G := by
    refine abs_le_of_sq_le_sq_lw ?_ (mul_nonneg (Real.sqrt_nonneg _) hG0)
    have hsq : (Real.sqrt (P * C.revolutionVolume) * G) ^ 2
        = P * C.revolutionVolume * G ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (mul_nonneg hP0 hV0)]
    rw [hsq]
    have hmono : massP g * C.revolutionVolume ≤ P * G ^ 2 * C.revolutionVolume :=
      mul_le_mul_of_nonneg_right hLgP hV0
    linarith [hcsm, hmono]
  -- `hBJ`
  have hBJ : |capJW C α td U - capJW C α td g - c ^ 2 * capJW C α td (oneP C)|
      ≤ A * |c| * G := by
    have hexp : capJW C α td U - capJW C α td g - c ^ 2 * capJW C α td (oneP C)
        = 2 * c * capJBilinW C α td g (oneP C) := by
      rw [← hU, capJW_add_smul_oneP]; ring
    rw [hexp, abs_mul, abs_mul, habs_two_lw]
    have hbil : |capJBilinW C α td g (oneP C)|
        ≤ (α * Real.sqrt (S * C.revolutionArea)
            + (m : ℝ) * α * Real.sqrt (P * C.revolutionVolume)) * G := by
      rw [capJBilinW]
      refine (abs_sub_le_lw _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg hα,
        abs_of_nonneg (mul_nonneg (Nat.cast_nonneg m) hα)]
      have h1 : α * |td.bdΓ g (oneP C)| ≤ α * (Real.sqrt (S * C.revolutionArea) * G) :=
        mul_le_mul_of_nonneg_left hbdcross hα
      have h2 : (m : ℝ) * α * |massBilinP g (oneP C)|
          ≤ (m : ℝ) * α * (Real.sqrt (P * C.revolutionVolume) * G) :=
        mul_le_mul_of_nonneg_left hmcross (mul_nonneg (Nat.cast_nonneg m) hα)
      linarith [h1, h2]
    calc 2 * |c| * |capJBilinW C α td g (oneP C)|
        ≤ 2 * |c| * ((α * Real.sqrt (S * C.revolutionArea)
            + (m : ℝ) * α * Real.sqrt (P * C.revolutionVolume)) * G) :=
          mul_le_mul_of_nonneg_left hbil (by positivity)
      _ = (2 * (α * Real.sqrt (S * C.revolutionArea)
            + (m : ℝ) * α * Real.sqrt (P * C.revolutionVolume))) * (|c| * G) := by ring
      _ ≤ A * (|c| * G) := mul_le_mul_of_nonneg_right hAe2 hcG
      _ = A * |c| * G := by ring
  -- `hNc`
  have hNc : |massP U - massP g - c ^ 2 * massP (oneP C)| ≤ A * |c| * G := by
    have hexp : massP U - massP g - c ^ 2 * massP (oneP C)
        = 2 * c * massBilinP g (oneP C) := by
      rw [← hU, massP_add_smul_oneP]; ring
    rw [hexp, abs_mul, abs_mul, habs_two_lw]
    calc 2 * |c| * |massBilinP g (oneP C)|
        ≤ 2 * |c| * (Real.sqrt (P * C.revolutionVolume) * G) :=
          mul_le_mul_of_nonneg_left hmcross (by positivity)
      _ = (2 * Real.sqrt (P * C.revolutionVolume)) * (|c| * G) := by ring
      _ ≤ A * (|c| * G) := mul_le_mul_of_nonneg_right hAe3 hcG
      _ = A * |c| * G := by ring
  -- the remaining hypotheses of the core
  have hLg : massP g ≤ A * G ^ 2 :=
    hLgP.trans (mul_le_mul_of_nonneg_right hAe4 hG2)
  have hVol : massP (oneP C) ≤ A := by rw [massP_oneP]; exact hAe5
  have hδA : |δ| ≤ A * R := hδ.trans (mul_le_mul_of_nonneg_right hAe6 hR.le)
  -- smallness of `R`
  rw [capR0W, ← hAdef] at hR0
  obtain ⟨hR1, hsmall⟩ := smallness_of_lt_lw hA0 hR hR0
  have hcore := cap_lower_weak_core C td hR hR1 hA0 hG0 hgrad hJg hBJ hNc hLg hVol hδA hsmall
  rw [capJW_oneP C hm hθ0 α td] at hcore
  rw [hDg, capLowerConstW, ← hAdef]
  exact hcore

/-- **`eq:cap-mass-bound` (`lem:cap`) for weak `H¹` functions**, in the variable `c = p/d_R`:
`N_cap[u] ≤ 2|𝒞| R c² + 2 C R ‖∇g‖²_{L²(𝒞)}`. -/
theorem cap_mass_bound_weak (C : Cap m)
    {CP C₁ : ℝ} (hpo : CapPoincare C CP) (hen : CapEntranceL2 C C₁)
    {ψ : EuclideanSpace ℝ (Fin m) → ℝ}
    (hψ : MemLp ψ 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)))
    (hψ1 : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ψ z ^ 2) = 1)
    {dR : ℝ} (hdR : dR = ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ψ z)
    (hdRge : Real.sqrt (omega m) / 2 ≤ dR)
    {R : ℝ} (hR : 0 ≤ R) (U : H1P C.body) :
    capMassScaledW R U
      ≤ 2 * C.revolutionVolume * R * cCoefW C ψ dR U ^ 2
        + 2 * capPoincareConstW C CP C₁ * R * dirichletP (gPartW C ψ dR U) := by
  have hω := omega_pos m
  have hdRpos : 0 < dR := by
    have : 0 < Real.sqrt (omega m) := Real.sqrt_pos.2 hω
    linarith
  set c := cCoefW C ψ dR U with hcdef
  set g := gPartW C ψ dR U with hgdef
  have horth : pCoefW C ψ g = 0 := pCoefW_gPartW C hen hψ hdR hdRpos.ne' U
  have hLgP : massP g ≤ capPoincareConstW C CP C₁ * dirichletP g :=
    weighted_poincare_lw C hpo hen hψ hψ1 hdR hdRge g horth
  have hsplit : massP U ≤ 2 * massP g + 2 * c ^ 2 * C.revolutionVolume :=
    massP_le_sub_constP C U c
  have hDg0 : 0 ≤ dirichletP g := dirichletP_nonneg g
  rw [capMassScaledW]
  have hstep : massP U ≤ 2 * (capPoincareConstW C CP C₁ * dirichletP g)
      + 2 * c ^ 2 * C.revolutionVolume := by linarith [hsplit, hLgP]
  nlinarith [mul_le_mul_of_nonneg_left hstep hR, hR]

/-! ## 11. The manuscript's `p`-form -/

/-- `ω_m/4 ≤ d_R²`, from `eq:d-R`. -/
theorem sq_dR_ge_lw {m : ℕ} {dR : ℝ} (hdRge : Real.sqrt (omega m) / 2 ≤ dR) :
    omega m / 4 ≤ dR ^ 2 := by
  have hω := omega_pos m
  have hs : (0 : ℝ) ≤ Real.sqrt (omega m) := Real.sqrt_nonneg _
  have h2 : (Real.sqrt (omega m) / 2) ^ 2 ≤ dR ^ 2 := by
    refine sq_le_sq' ?_ hdRge
    linarith
  have h3 : (Real.sqrt (omega m) / 2) ^ 2 = omega m / 4 := by
    rw [div_pow, Real.sq_sqrt hω.le]; norm_num
  linarith

/-- **`eq:cap-lower` exactly as in the manuscript**, in the variable
`p = ⟨Tr_Σ U, Ψ_R⟩_{L²(Σ)}`:

`E_cap[u] ≥ (β(𝒞) − C'ω_m⁻¹ R) |p|² + (2R)⁻¹ ‖∇g‖²_{L²(𝒞)}`. -/
theorem cap_lower_weak_p (C : Cap m) (hm : 1 ≤ m) (hθ0 : 0 ≤ C.θ 0) (td : CapTraceData C)
    {CP C₁ Cδ α : ℝ} (hpo : CapPoincare C CP) (hen : CapEntranceL2 C C₁)
    (hCδ : 0 ≤ Cδ) (hα : 0 ≤ α) (hβ : 0 ≤ C.beta α)
    {ψ : EuclideanSpace ℝ (Fin m) → ℝ}
    (hψ : MemLp ψ 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)))
    (hψ1 : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ψ z ^ 2) = 1)
    {dR : ℝ} (hdR : dR = ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ψ z)
    (hdRge : Real.sqrt (omega m) / 2 ≤ dR)
    {R δ : ℝ} (hR : 0 < R) (hR0 : R < capR0W C α td CP C₁ Cδ) (hδ : |δ| ≤ Cδ * R)
    (hBR : capLowerConstW C α td CP C₁ Cδ * R ≤ omega m * C.beta α)
    (U : H1P C.body) :
    dirichletP (gPartW C ψ dR U) / (2 * R)
        + (C.beta α - capLowerConstW C α td CP C₁ Cδ / omega m * R) * pCoefW C ψ U ^ 2
      ≤ capEnergyW C α td R δ U := by
  have hω := omega_pos m
  have hdRpos : 0 < dR := by
    have : 0 < Real.sqrt (omega m) := Real.sqrt_pos.2 hω
    linarith
  have hdR2pos : (0 : ℝ) < dR ^ 2 := pow_pos hdRpos 2
  have hdRsq : dR ^ 2 ≤ omega m := by rw [hdR]; exact dR_sq_le_omega_lw hψ hψ1
  have hA0 := (capConstW_ge C hα td hpo.nonneg hen.nonneg hCδ).1
  have hB0 : 0 ≤ capLowerConstW C α td CP C₁ Cδ := by
    rw [capLowerConstW]
    have h1 : 0 ≤ capConstW C α td CP C₁ Cδ + capConstW C α td CP C₁ Cδ ^ 2 := by
      nlinarith [sq_nonneg (capConstW C α td CP C₁ Cδ)]
    nlinarith [h1]
  have hR1 : R ≤ 1 := by
    have : capR0W C α td CP C₁ Cδ ≤ 1 := by rw [capR0W]; exact min_le_left _ _
    linarith
  have hp : pCoefW C ψ U ^ 2 ≤ (omega m + 0 * R ^ 2) * cCoefW C ψ dR U ^ 2 := by
    rw [cCoefW, div_pow]
    simp only [zero_mul, add_zero]
    rw [mul_div_assoc', le_div_iff₀ hdR2pos]
    nlinarith [sq_nonneg (pCoefW C ψ U), hdRsq]
  have hlow := @lower_c_to_p (omega m) (C.beta α) (capLowerConstW C α td CP C₁ Cδ)
    (pCoefW C ψ U) (cCoefW C ψ dR U) 0 R hω hβ hB0 le_rfl hR.le hR1 hBR hp
  have hsimp : (capLowerConstW C α td CP C₁ Cδ + C.beta α * 0) / omega m
      = capLowerConstW C α td CP C₁ Cδ / omega m := by ring_nf
  rw [hsimp] at hlow
  have hmain := cap_lower_weak C hm hθ0 td hpo hen hCδ hα hψ hψ1 hdR hdRge hR hR0 hδ U
  linarith [hmain, hlow]

/-- **`eq:cap-mass-bound` exactly as in the manuscript**, in the variable `p`:
`N_cap[u] ≤ 8|𝒞|ω_m⁻¹ R |p|² + 2C R ‖∇g‖²_{L²(𝒞)}`. -/
theorem cap_mass_bound_weak_p (C : Cap m)
    {CP C₁ : ℝ} (hpo : CapPoincare C CP) (hen : CapEntranceL2 C C₁)
    {ψ : EuclideanSpace ℝ (Fin m) → ℝ}
    (hψ : MemLp ψ 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)))
    (hψ1 : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ψ z ^ 2) = 1)
    {dR : ℝ} (hdR : dR = ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ψ z)
    (hdRge : Real.sqrt (omega m) / 2 ≤ dR)
    {R : ℝ} (hR : 0 ≤ R) (U : H1P C.body) :
    capMassScaledW R U
      ≤ 8 * C.revolutionVolume / omega m * R * pCoefW C ψ U ^ 2
        + 2 * capPoincareConstW C CP C₁ * R * dirichletP (gPartW C ψ dR U) := by
  have hω := omega_pos m
  have hV0 : 0 ≤ C.revolutionVolume := revolutionVolume_nonneg_lw C
  have hdRpos : 0 < dR := by
    have : 0 < Real.sqrt (omega m) := Real.sqrt_pos.2 hω
    linarith
  have hdR2pos : (0 : ℝ) < dR ^ 2 := pow_pos hdRpos 2
  have hge := sq_dR_ge_lw (m := m) (dR := dR) hdRge
  have hbase := cap_mass_bound_weak C hpo hen hψ hψ1 hdR hdRge hR U
  have hc2 : cCoefW C ψ dR U ^ 2 ≤ 4 / omega m * pCoefW C ψ U ^ 2 := by
    rw [cCoefW, div_pow, div_le_iff₀ hdR2pos]
    have hkey : pCoefW C ψ U ^ 2 * omega m ≤ 4 * pCoefW C ψ U ^ 2 * dR ^ 2 := by
      nlinarith [sq_nonneg (pCoefW C ψ U), hge]
    have hrw : 4 / omega m * pCoefW C ψ U ^ 2 * dR ^ 2
        = 4 * pCoefW C ψ U ^ 2 * dR ^ 2 / omega m := by field_simp
    rw [hrw, le_div_iff₀ hω]
    linarith [hkey]
  have hstep : 2 * C.revolutionVolume * R * cCoefW C ψ dR U ^ 2
      ≤ 8 * C.revolutionVolume / omega m * R * pCoefW C ψ U ^ 2 := by
    have hcoef : (0 : ℝ) ≤ 2 * C.revolutionVolume * R := by positivity
    have := mul_le_mul_of_nonneg_left hc2 hcoef
    calc 2 * C.revolutionVolume * R * cCoefW C ψ dR U ^ 2
        ≤ 2 * C.revolutionVolume * R * (4 / omega m * pCoefW C ψ U ^ 2) := this
      _ = 8 * C.revolutionVolume / omega m * R * pCoefW C ψ U ^ 2 := by
          field_simp; ring
  linarith [hbase, hstep]

/-! ## 12. Specialisation to the transverse ground state `Ψ_R`

The hypotheses `hψ1`, `hdRge` and `hδ` of the theorems above are supplied, for
`ψ = Ψ_R = transLift m R ψ_R`, by `RobinCaps.ThinDomain.TransverseExpansionData`
(`eq:d-R` and `eq:nu-expansion` of `lem:transverse`) together with the `L²`-normalisation
`RobinCaps.ThinDomain.integral_transLift_sq`. -/

variable {α R : ℝ} {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}

/-- `Ψ_R` is in `L²(B_m(1))`: it is continuous, hence bounded on the unit ball. -/
theorem memLp_transLift_lw (gsr : TransverseGroundStateReg m α R bd) :
    MemLp (transLift m R gsr.psi) 2
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)) := by
  have hcont : Continuous (transLift m R gsr.psi) :=
    (contDiff_transLift (ψ := gsr.psi) gsr.psiC1).continuous
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) 1).exists_bound_of_continuousOn
    hcont.continuousOn
  refine MemLp.of_bound hcont.aestronglyMeasurable M ?_
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  exact hM z (ball_subset_closedBall hz)

/-- `|δ_R| ≤ C_exp R` for `δ_R = Rν_R − mα`, from `eq:nu-expansion`. -/
theorem abs_delta_le_lw {Cexp : ℝ} {gsr : TransverseGroundStateReg m α R bd}
    (ted : TransverseExpansionData m α R gsr Cexp) (hR : 0 < R) :
    |R * gsr.nu - (m : ℝ) * α| ≤ Cexp * R := by
  have h := ted.nuExp
  have hid : R ^ 2 * gsr.nu - (m : ℝ) * α * R = R * (R * gsr.nu - (m : ℝ) * α) := by ring
  rw [hid, abs_mul, abs_of_pos hR] at h
  have h2 : R * |R * gsr.nu - (m : ℝ) * α| ≤ R * (Cexp * R) := by linarith [h]
  exact le_of_mul_le_mul_left h2 hR

theorem Cexp_nonneg_lw {Cexp : ℝ} {gsr : TransverseGroundStateReg m α R bd}
    (ted : TransverseExpansionData m α R gsr Cexp) (hR : 0 < R) : 0 ≤ Cexp := by
  have h := ted.nuExp
  have h0 : (0 : ℝ) ≤ |R ^ 2 * gsr.nu - (m : ℝ) * α * R| := abs_nonneg _
  have hR2 : (0 : ℝ) < R ^ 2 := pow_pos hR 2
  nlinarith [h, h0, hR2]

/-- **`eq:cap-lower` for `ψ = Ψ_R` and `δ = δ_R = Rν_R − mα`.** -/
theorem cap_lower_weak_transverse (C : Cap m) (hm : 1 ≤ m) (hθ0 : 0 ≤ C.θ 0)
    (td : CapTraceData C) {CP C₁ : ℝ} (hpo : CapPoincare C CP) (hen : CapEntranceL2 C C₁)
    (hα : 0 ≤ α) (hR : 0 < R) {Cexp : ℝ} {gsr : TransverseGroundStateReg m α R bd}
    (ted : TransverseExpansionData m α R gsr Cexp)
    (hR0 : R < capR0W C α td CP C₁ Cexp) (U : H1P C.body) :
    dirichletP (gPartW C (transLift m R gsr.psi)
        (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gsr.psi y) U) / (2 * R)
      + (omega m * C.beta α - capLowerConstW C α td CP C₁ Cexp * R)
        * cCoefW C (transLift m R gsr.psi)
            (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gsr.psi y) U ^ 2
      ≤ capEnergyW C α td R (R * gsr.nu - (m : ℝ) * α) U :=
  cap_lower_weak C hm hθ0 td hpo hen (Cexp_nonneg_lw ted hR) hα (memLp_transLift_lw gsr)
    (integral_transLift_sq hR gsr) rfl ted.dR_ge hR hR0 (abs_delta_le_lw ted hR) U

end

end Cap
end RobinCaps
