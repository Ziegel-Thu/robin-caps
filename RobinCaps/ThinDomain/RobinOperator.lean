import RobinCaps.ThinDomain.EigenThin
import RobinCaps.Sobolev.ConvexDensity

/-!
# The Robin Laplacian on the thin domain, packaged in "graph" form

This file packages the Robin boundary value problem

`-Δu = f` in `Ω`, `∂ₙu + α u = 0` on `∂Ω` (weakly),

for `Ω := thinDomain Cm Cp L R`, as a relation between `H1P Ω` and `L²(Ω)` — the graph of the
(unbounded, densely defined) Robin realization of `-Δ` — rather than through an abstract
unbounded-operator library, which mathlib `v4.26.0` does not provide in the generality needed
here. The closed form defining the operator is the Robin form of `ThinDomain/H1PQuotient.lean`,

`q(u,v) = dirichletBilinP u v + α · td.bd u v`,

with `td : TraceData Cm Cp L R` the boundary pairing of `ThinDomain/Boundary.lean` and
`α : ℝ` the Robin parameter.

## Contents

* `IsRobinImage_rop td α u f` — the weak formulation "`u` is in the domain of the Robin
  Laplacian and its image is `f`", i.e. `f ∈ L²(Ω)` and `q(u,v) = ∫_Ω f v` for every test
  element `v : H1P Ω`.
* `robinDomain_rop td α` — the domain of the Robin Laplacian, bundled as a submodule of
  `H1P Ω` (nonempty: it contains `0`, and is closed under `+` and scalar multiples by
  `isRobinImage_add_rop`, `isRobinImage_smul_rop`).
* `isRobinImage_unique_rop` — **uniqueness of the image**: if `u` has both `f` and `g` as
  weak images then `f =ᵐ g` on `Ω`. This is the fundamental lemma of the calculus of
  variations on the open set `Ω`
  (`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`), tested against
  `H1P.ofCompactSupport Ω φ` for smooth compactly supported `φ` with `tsupport φ ⊆ Ω`; no
  transport to an inner-product space is needed since the lemma already holds on the
  finite-dimensional normed space `CapSpace m` for an arbitrary Borel measure.
* `isRobinImage_add_rop`, `isRobinImage_smul_rop` — linearity of the relation in `(u,f)`.
* `isRobinImage_symm_rop` — **symmetry** of the (formal) operator:
  `∫_Ω f w = ∫_Ω u g` whenever `u ↦ f` and `w ↦ g`.
* `isRobinImage_nonneg_rop` — **nonnegativity**: `0 ≤ ∫_Ω f u` whenever `u ↦ f` and `α ≥ 0`.
* `isRobinImage_eigen_iff_rop` — `u ↦ μ • u.toFun` iff `u` is a weak Robin eigenfunction with
  eigenvalue `μ`.
* `eigen_quotient_rop` — the weak Robin eigenvalue equation on `H1P Ω` is equivalent to the
  corresponding equation on the quotient `H1PQ Ω` against the bundled compact-form setting
  `robinSetting_eth` of `ThinDomain/EigenThin.lean`.
* `mk_ne_zero_iff_rop` — an element of `H1PQ Ω` coming from `u : H1P Ω` is nonzero iff
  `u` has positive mass, linking `H1PQuotient.lean`'s positive-definiteness of the mass
  (`massPQ_pos`) with the concrete representative `u`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

open MeasureTheory Set Filter
open RobinCaps.Domain RobinCaps.Cap

namespace RobinCaps.ThinDomain

variable {m : ℕ} {Cm Cp : Cap m} {L R : ℝ}

/-! ## The weak Robin image relation and its domain -/

/-- **`u` is in the domain of the Robin Laplacian with image `f`.**

`f ∈ L²(Ω)` and, for every `v : H1P Ω`,

`∫_Ω (∂ₓu ∂ₓv + ⟪∇_z u, ∇_z v⟫) + α ∫_{∂Ω} (Tr u)(Tr v) = ∫_Ω f v`,

the weak formulation of `-Δu = f` in `Ω` together with the Robin condition `∂ₙu + α u = 0` on
`∂Ω`. -/
def IsRobinImage_rop (td : TraceData Cm Cp L R) (α : ℝ) (u : H1P (thinDomain Cm Cp L R))
    (f : CapSpace m → ℝ) : Prop :=
  MemLp f 2 (volume.restrict (thinDomain Cm Cp L R)) ∧
    ∀ v : H1P (thinDomain Cm Cp L R),
      dirichletBilinP u v + α * td.bd u v = ∫ p in thinDomain Cm Cp L R, f p * v.toFun p

/-- The zero element of `H1P Ω` is in the domain, with image `0`. -/
theorem isRobinImage_zero_rop (td : TraceData Cm Cp L R) (α : ℝ) :
    IsRobinImage_rop td α (0 : H1P (thinDomain Cm Cp L R)) (fun _ => 0) := by
  refine ⟨MemLp.zero, fun v => ?_⟩
  have h1 : dirichletBilinP (0 : H1P (thinDomain Cm Cp L R)) v = 0 := by
    rw [← dirichletBilinPₗ_apply]; simp
  have h2 : td.bd (0 : H1P (thinDomain Cm Cp L R)) v = 0 := by simp
  rw [h1, h2]
  simp

/-- **Linearity of the image relation, in addition.** -/
theorem isRobinImage_add_rop {td : TraceData Cm Cp L R} {α : ℝ}
    {u u' : H1P (thinDomain Cm Cp L R)} {f f' : CapSpace m → ℝ}
    (hf : IsRobinImage_rop td α u f) (hf' : IsRobinImage_rop td α u' f') :
    IsRobinImage_rop td α (u + u') (f + f') := by
  obtain ⟨hL2, heq⟩ := hf
  obtain ⟨hL2', heq'⟩ := hf'
  refine ⟨hL2.add hL2', fun v => ?_⟩
  have e1 := heq v
  have e2 := heq' v
  have hbil : dirichletBilinP (u + u') v = dirichletBilinP u v + dirichletBilinP u' v :=
    dirichletBilinP_add_left u u' v
  have hbd : td.bd (u + u') v = td.bd u v + td.bd u' v := TraceData.bd_add_left td u u' v
  have hInt1 : Integrable (fun p => f p * v.toFun p) (volume.restrict (thinDomain Cm Cp L R)) :=
    hL2.integrable_mul v.memL2
  have hInt2 : Integrable (fun p => f' p * v.toFun p) (volume.restrict (thinDomain Cm Cp L R)) :=
    hL2'.integrable_mul v.memL2
  have hrhs : (∫ p in thinDomain Cm Cp L R, (f + f') p * v.toFun p)
      = (∫ p in thinDomain Cm Cp L R, f p * v.toFun p)
        + ∫ p in thinDomain Cm Cp L R, f' p * v.toFun p := by
    rw [← integral_add hInt1 hInt2]
    exact integral_congr_ae (.of_forall fun p => by simp only [Pi.add_apply]; ring)
  calc dirichletBilinP (u + u') v + α * td.bd (u + u') v
      = dirichletBilinP u v + α * td.bd u v + (dirichletBilinP u' v + α * td.bd u' v) := by
        rw [hbil, hbd]; ring
    _ = (∫ p in thinDomain Cm Cp L R, f p * v.toFun p)
          + ∫ p in thinDomain Cm Cp L R, f' p * v.toFun p := by rw [e1, e2]
    _ = ∫ p in thinDomain Cm Cp L R, (f + f') p * v.toFun p := hrhs.symm

/-- **Linearity of the image relation, in scalar multiples.** -/
theorem isRobinImage_smul_rop (c : ℝ) {td : TraceData Cm Cp L R} {α : ℝ}
    {u : H1P (thinDomain Cm Cp L R)} {f : CapSpace m → ℝ} (hf : IsRobinImage_rop td α u f) :
    IsRobinImage_rop td α (c • u) (c • f) := by
  obtain ⟨hL2, heq⟩ := hf
  refine ⟨hL2.const_smul c, fun v => ?_⟩
  have e := heq v
  have hbil : dirichletBilinP (c • u) v = c * dirichletBilinP u v := dirichletBilinP_smul_left c u v
  have hbd : td.bd (c • u) v = c * td.bd u v := TraceData.bd_smul_left td c u v
  have hrhs : (∫ p in thinDomain Cm Cp L R, (c • f) p * v.toFun p)
      = c * ∫ p in thinDomain Cm Cp L R, f p * v.toFun p := by
    rw [← integral_const_mul]
    exact integral_congr_ae (.of_forall fun p => by
      simp only [Pi.smul_apply, smul_eq_mul]; ring)
  calc dirichletBilinP (c • u) v + α * td.bd (c • u) v
      = c * (dirichletBilinP u v + α * td.bd u v) := by rw [hbil, hbd]; ring
    _ = c * ∫ p in thinDomain Cm Cp L R, f p * v.toFun p := by rw [e]
    _ = ∫ p in thinDomain Cm Cp L R, (c • f) p * v.toFun p := hrhs.symm

/-- **The domain of the Robin Laplacian**, bundled as a submodule of `H1P Ω`. -/
def robinDomain_rop (td : TraceData Cm Cp L R) (α : ℝ) :
    Submodule ℝ (H1P (thinDomain Cm Cp L R)) where
  carrier := {u | ∃ f, IsRobinImage_rop td α u f}
  zero_mem' := ⟨fun _ => 0, isRobinImage_zero_rop td α⟩
  add_mem' := by
    rintro u v ⟨f, hf⟩ ⟨g, hg⟩
    exact ⟨f + g, isRobinImage_add_rop hf hg⟩
  smul_mem' := by
    rintro c u ⟨f, hf⟩
    exact ⟨c • f, isRobinImage_smul_rop c hf⟩

/-! ## Uniqueness of the image -/

/-- **Uniqueness of the weak image.**  If `u` has both `f` and `g` as weak Robin images then
`f =ᵐ g` on `Ω`.  Proved by testing the defining equation against `v := H1P.ofCompactSupport Ω
φ` for `φ` smooth, compactly supported, with `tsupport φ ⊆ Ω`, which gives `∫_Ω (f-g) φ = 0`
for all such `φ`; the fundamental lemma of the calculus of variations on the open set `Ω`
(`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`, available directly on the
finite-dimensional normed space `CapSpace m` for the measure `volume.restrict Ω`, exactly as
already used for the uniqueness of the weak gradient in `ThinDomain/H1P.lean`) concludes. -/
theorem isRobinImage_unique_rop (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    {td : TraceData Cm Cp L R} {α : ℝ} {u : H1P (thinDomain Cm Cp L R)} {f g : CapSpace m → ℝ}
    (hf : IsRobinImage_rop td α u f) (hg : IsRobinImage_rop td α u g) :
    f =ᵐ[volume.restrict (thinDomain Cm Cp L R)] g := by
  have hΩ : IsOpen (thinDomain Cm Cp L R) := isOpen_thinDomain hR hL
  obtain ⟨hfL2, hfeq⟩ := hf
  obtain ⟨hgL2, hgeq⟩ := hg
  have hloc : LocallyIntegrableOn (fun p => f p - g p) (thinDomain Cm Cp L R)
      (volume.restrict (thinDomain Cm Cp L R)) := by
    have hmem : MemLp (fun p => f p - g p) 2 (volume.restrict (thinDomain Cm Cp L R)) :=
      hfL2.sub hgL2
    exact (hmem.locallyIntegrable (by norm_num)).locallyIntegrableOn (thinDomain Cm Cp L R)
  have hvan : ∀ᵐ p ∂(volume.restrict (thinDomain Cm Cp L R)),
      p ∈ thinDomain Cm Cp L R → f p - g p = 0 := by
    refine hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc ?_
    intro φ hφ hφc hφs
    have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
    set v : H1P (thinDomain Cm Cp L R) := H1P.ofCompactSupport (thinDomain Cm Cp L R) φ hφ1 hφc
      with hvdef
    have hv : v.toFun = φ := H1P.ofCompactSupport_toFun (thinDomain Cm Cp L R) φ hφ1 hφc
    have e1 := hfeq v
    have e2 := hgeq v
    rw [hv] at e1 e2
    have heqfg : (∫ p in thinDomain Cm Cp L R, f p * φ p)
        = ∫ p in thinDomain Cm Cp L R, g p * φ p := by rw [← e1, ← e2]
    have hInt1 : Integrable (fun p => f p * φ p) (volume.restrict (thinDomain Cm Cp L R)) :=
      hfL2.integrable_mul (memLp_two_of_testP hφ hφc)
    have hInt2 : Integrable (fun p => g p * φ p) (volume.restrict (thinDomain Cm Cp L R)) :=
      hgL2.integrable_mul (memLp_two_of_testP hφ hφc)
    have hsplit : (∫ p, φ p • (f p - g p) ∂(volume.restrict (thinDomain Cm Cp L R)))
        = (∫ p in thinDomain Cm Cp L R, f p * φ p)
          - ∫ p in thinDomain Cm Cp L R, g p * φ p := by
      rw [← integral_sub hInt1 hInt2]
      exact integral_congr_ae (.of_forall fun p => by simp only [smul_eq_mul]; ring)
    rw [hsplit, heqfg, sub_self]
  filter_upwards [hvan, ae_restrict_mem hΩ.measurableSet] with p hp hpΩ
  exact sub_eq_zero.1 (hp hpΩ)

/-! ## Symmetry and nonnegativity -/

/-- **Symmetry of the (formal) Robin operator.** -/
theorem isRobinImage_symm_rop {td : TraceData Cm Cp L R} {α : ℝ}
    {u w : H1P (thinDomain Cm Cp L R)} {f g : CapSpace m → ℝ}
    (hf : IsRobinImage_rop td α u f) (hg : IsRobinImage_rop td α w g) :
    (∫ p in thinDomain Cm Cp L R, f p * w.toFun p)
      = ∫ p in thinDomain Cm Cp L R, u.toFun p * g p := by
  obtain ⟨_, heq⟩ := hf
  obtain ⟨_, heq'⟩ := hg
  have e1 := heq w
  have e2 := heq' u
  rw [dirichletBilinP_comm w u, td.bd_symm w u] at e2
  have hAB : (∫ p in thinDomain Cm Cp L R, f p * w.toFun p)
      = ∫ p in thinDomain Cm Cp L R, g p * u.toFun p := by rw [← e1, e2]
  rw [hAB]
  exact integral_congr_ae (.of_forall fun p => mul_comm (g p) (u.toFun p))

/-- **Nonnegativity of the (formal) Robin operator**, for `α ≥ 0`. -/
theorem isRobinImage_nonneg_rop {td : TraceData Cm Cp L R} {α : ℝ} (hα : 0 ≤ α)
    {u : H1P (thinDomain Cm Cp L R)} {f : CapSpace m → ℝ} (hf : IsRobinImage_rop td α u f) :
    0 ≤ ∫ p in thinDomain Cm Cp L R, f p * u.toFun p := by
  obtain ⟨_, heq⟩ := hf
  have e := heq u
  rw [← e]
  have h1 : 0 ≤ dirichletBilinP u u := by rw [dirichletBilinP_self]; exact dirichletP_nonneg u
  have h2 : 0 ≤ α * td.bd u u := mul_nonneg hα (td.bd_nonneg u)
  linarith

/-! ## The weak eigenvalue equation -/

/-- **`u` is a weak Robin eigenfunction with eigenvalue `μ` iff its image under the Robin
operator is `μ • u.toFun`.**  The `MemLp` requirement of `IsRobinImage_rop` is automatic here,
from `u.memL2`. -/
theorem isRobinImage_eigen_iff_rop {td : TraceData Cm Cp L R} {α μ : ℝ}
    {u : H1P (thinDomain Cm Cp L R)} :
    IsRobinImage_rop td α u (μ • u.toFun) ↔
      ∀ v : H1P (thinDomain Cm Cp L R),
        dirichletBilinP u v + α * td.bd u v = μ * massBilinP u v := by
  constructor
  · rintro ⟨_, heq⟩ v
    have e := heq v
    rw [e]
    unfold massBilinP
    rw [← integral_const_mul]
    exact integral_congr_ae (.of_forall fun p => by
      simp only [Pi.smul_apply, smul_eq_mul]; ring)
  · intro h
    refine ⟨u.memL2.const_smul μ, fun v => ?_⟩
    rw [h v]
    unfold massBilinP
    rw [← integral_const_mul]
    exact integral_congr_ae (.of_forall fun p => by
      simp only [Pi.smul_apply, smul_eq_mul]; ring)

/-! ## Link with the abstract compact-form setting on the quotient -/

/-- **The weak Robin eigenvalue equation on `H1P Ω` descends to the quotient `H1PQ Ω`**,
against the bundled energy/mass pair `robinSetting_eth`. -/
theorem eigen_quotient_rop (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (td : TraceData Cm Cp L R)
    {α : ℝ} (hα : 0 ≤ α) (hrel : RellichEmbeddingP (thinDomain Cm Cp L R))
    (hcomp : H1PCompleteProp (thinDomain Cm Cp L R)) (u : H1P (thinDomain Cm Cp L R)) (μ : ℝ) :
    (∀ v : H1P (thinDomain Cm Cp L R),
        dirichletBilinP u v + α * td.bd u v = μ * massBilinP u v) ↔
      (∀ w : H1PQ (thinDomain Cm Cp L R),
        (robinSetting_eth hR hL td hα hrel hcomp).Q (Submodule.Quotient.mk u) w
          = μ * (robinSetting_eth hR hL td hα hrel hcomp).N (Submodule.Quotient.mk u) w) := by
  constructor
  · intro h w
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (nullAEP (thinDomain Cm Cp L R)) w
    rw [robinSetting_Q_eth, robinSetting_N_eth]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, dirichletBilinPQ_mk,
      bdQ_mk, massBilinPQ_mk]
    exact h v
  · intro h v
    have hh := h (Submodule.Quotient.mk v)
    rw [robinSetting_Q_eth, robinSetting_N_eth] at hh
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, dirichletBilinPQ_mk,
      bdQ_mk, massBilinPQ_mk] at hh
    exact hh

/-- **A representative's class in `H1PQ Ω` is nonzero iff it has positive mass.**  The forward
direction is `massPQ_pos` unfolded along `massPQ_mk`; the converse is proved by contraposition,
using that an element of `nullAEP Ω` has a.e.-vanishing representative, hence zero mass. -/
theorem mk_ne_zero_iff_rop (u : H1P (thinDomain Cm Cp L R)) :
    (Submodule.Quotient.mk u : H1PQ (thinDomain Cm Cp L R)) ≠ 0 ↔ 0 < massP u := by
  constructor
  · intro hne
    have h := massPQ_pos (Submodule.Quotient.mk u) hne
    rwa [massPQ_mk] at h
  · intro hpos heq
    have hmem : u ∈ nullAEP (thinDomain Cm Cp L R) :=
      (Submodule.Quotient.mk_eq_zero (nullAEP (thinDomain Cm Cp L R))).mp heq
    have hu0 : u.toFun =ᵐ[volume.restrict (thinDomain Cm Cp L R)] 0 := hmem
    have hz : massP u = 0 := by
      unfold massP
      have heq2 : (fun p => u.toFun p ^ 2)
          =ᵐ[volume.restrict (thinDomain Cm Cp L R)] fun _ => (0 : ℝ) := by
        filter_upwards [hu0] with p hp
        simp only [Pi.zero_apply] at hp
        simp [hp]
      rw [integral_congr_ae heq2, integral_zero]
    linarith

end RobinCaps.ThinDomain

end
