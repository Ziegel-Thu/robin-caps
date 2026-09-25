import RobinCaps.ThinDomain.EigenIface
import RobinCaps.Spectrum.CompactForm
import RobinCaps.ThinDomain.Eigen
import RobinCaps.Compact.RayleighAlgebra

/-!
# U-EIGEN-THIN: the compact form setting on `H1PQ (thinDomain Cm Cp L R)`, and the genuine
# Robin eigenfunctions of the thin domain

This file joins the two analytic interface `Prop`s of `ThinDomain/EigenIface.lean`
(`RellichEmbeddingP`, `H1PCompleteProp`) and the abstract wave-12 spectral engine of
`Spectrum/CompactForm.lean` (`CompactFormSetting`, `EigenFamilyProp`) with the concrete Robin
form `robinFormPQ` and variational eigenvalues `lambdaThin` of `ThinDomain/H1PQuotient.lean` and
`ThinDomain/Eigen.lean`.

## Contents

* `robinSetting_eth` — the **compact form setting** on `W := H1PQ (thinDomain Cm Cp L R)` with
  energy `Q = dirichletBilinPQ hΩ + α • bdQ td.bd td.vanishesOnNullAEP` (the Robin form,
  bundled) and mass `N = massBilinPQ`.  Symmetry and nonnegativity/positivity are algebraic
  consequences of `H1PQuotient.lean`; `complete` is assembled from `H1PCompleteProp` together
  with the two-sided estimate `dirichletP u + massP u ≤ Q[u] + N[u] ≤ (1 + α C) (dirichletP u +
  massP u)` coming from the boundary form's nonnegativity and `TraceData.trace_ineq`; `compact`
  is assembled from `RellichEmbeddingP` together with the elementary inequality
  `(a - c)² ≤ 2 (a - b)² + 2 (b - c)²`.
* `robinSetting_Q_eth`, `robinSetting_N_eth` — the (defeq, `rfl`-provable) unfolding lemmas for
  the energy and mass fields of `robinSetting_eth`, used to unfold the bundled forms back into
  `dirichletBilinP`, `td.bd` and `massBilinP` on representatives.
* `minmax_robinSetting_eth` — the abstract min–max values of `robinSetting_eth` are exactly the
  manuscript's variational eigenvalues `lambdaThin hR hL td α j`.
* `exists_eigenfunctions_eth` — combining `EigenFamilyProp (robinSetting_eth …) j` with a
  `j`-dimensional subspace of `H1PQ (thinDomain Cm Cp L R)` produces `j` genuine
  `H1P`-representative eigenfunctions of the thin-domain Robin problem: `N`-orthonormal,
  solving the weak eigenvalue equation with eigenvalue `lambdaThin hR hL td α (a+1)`, and with
  nondecreasing eigenvalues.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file; `RellichEmbeddingP`,
`H1PCompleteProp` and `EigenFamilyProp` are taken as hypotheses (proved elsewhere by parallel
workers).
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Set Filter Topology
open RobinCaps.Domain RobinCaps.Cap

namespace RobinCaps.ThinDomain

variable {m : ℕ} {Cm Cp : Cap m} {L R : ℝ}

/-! ## The compact form setting on `H1PQ (thinDomain Cm Cp L R)` -/

/-- **The compact form setting of the thin-domain Robin problem.**

The energy is the Robin form `dirichletBilinPQ hΩ + α • bdQ td.bd td.vanishesOnNullAEP`
(bundled, so that `RobinCaps.Spectrum.bddAbove_ratio_of_bilinear`-style arguments apply) and the
mass is `massBilinPQ`.  Symmetry is inherited from `dirichletBilinP_comm`, `td.bd_symm` and
`massBilinP_comm`; nonnegativity of the energy from `robinFormPQ_nonneg`; positivity of the mass
from `massPQ_pos`.  Completeness and compactness are the substance of the file: they are
assembled from the two analytic hypotheses `hcomp` (`H1PCompleteProp`) and `hrel`
(`RellichEmbeddingP`) via the two-sided energy-norm estimate coming from `td.bd_nonneg`,
`hα` and `td.trace_ineq`. -/
def robinSetting_eth (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (td : TraceData Cm Cp L R)
    {α : ℝ} (hα : 0 ≤ α) (hrel : RellichEmbeddingP (thinDomain Cm Cp L R))
    (hcomp : H1PCompleteProp (thinDomain Cm Cp L R)) :
    RobinCaps.Spectrum.CompactFormSetting (H1PQ (thinDomain Cm Cp L R)) :=
  have hΩ : IsOpen (thinDomain Cm Cp L R) := isOpen_thinDomain hR hL
  { Q := dirichletBilinPQ hΩ + α • bdQ td.bd td.vanishesOnNullAEP
    N := massBilinPQ
    Q_symm := by
      intro x y
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective (nullAEP (thinDomain Cm Cp L R)) x
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective (nullAEP (thinDomain Cm Cp L R)) y
      simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, dirichletBilinPQ_mk,
        bdQ_mk]
      rw [dirichletBilinP_comm, td.bd_symm]
    N_symm := by
      intro x y
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective (nullAEP (thinDomain Cm Cp L R)) x
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective (nullAEP (thinDomain Cm Cp L R)) y
      simp only [massBilinPQ_mk]
      exact massBilinP_comm a b
    Q_nonneg := by
      intro x
      rw [← robinFormPQ_eq_bilin]
      exact robinFormPQ_nonneg hΩ td.bd td.vanishesOnNullAEP hα td.bd_nonneg x
    N_pos := fun x hx => massPQ_pos x hx
    complete := by
      intro w hw
      choose u hu using
        fun k => Submodule.Quotient.mk_surjective (nullAEP (thinDomain Cm Cp L R)) (w k)
      have hCauchy : ∀ η : ℝ, 0 < η → ∃ K : ℕ, ∀ k l, K ≤ k → K ≤ l →
          massP (u k - u l) + dirichletP (u k - u l) ≤ η := by
        intro η hη
        obtain ⟨K, hK⟩ := hw η hη
        refine ⟨K, fun k l hk hl => ?_⟩
        have he := hK k l hk hl
        rw [show w k - w l = Submodule.Quotient.mk (u k - u l) by
          rw [← hu k, ← hu l, Submodule.Quotient.mk_sub]] at he
        simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, dirichletBilinPQ_mk,
          bdQ_mk, massBilinPQ_mk, dirichletBilinP_self, massBilinP_self] at he
        linarith [mul_nonneg hα (td.bd_nonneg (u k - u l))]
      obtain ⟨v, hv⟩ := hcomp u hCauchy
      obtain ⟨C, hC0, hCbound⟩ := td.trace_ineq
      refine ⟨Submodule.Quotient.mk v, ?_⟩
      have hrw : ∀ k, w k - Submodule.Quotient.mk v = Submodule.Quotient.mk (u k - v) := by
        intro k; rw [← hu k, Submodule.Quotient.mk_sub]
      have hval : ∀ k,
          (dirichletBilinPQ hΩ + α • bdQ td.bd td.vanishesOnNullAEP)
              (w k - Submodule.Quotient.mk v) (w k - Submodule.Quotient.mk v)
            + massBilinPQ (w k - Submodule.Quotient.mk v) (w k - Submodule.Quotient.mk v)
          = dirichletP (u k - v) + α * td.bd (u k - v) (u k - v) + massP (u k - v) := by
        intro k
        rw [hrw k]
        simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, dirichletBilinPQ_mk,
          bdQ_mk, massBilinPQ_mk, dirichletBilinP_self, massBilinP_self]
      have hupper : ∀ k,
          (dirichletBilinPQ hΩ + α • bdQ td.bd td.vanishesOnNullAEP)
              (w k - Submodule.Quotient.mk v) (w k - Submodule.Quotient.mk v)
            + massBilinPQ (w k - Submodule.Quotient.mk v) (w k - Submodule.Quotient.mk v)
          ≤ (1 + α * C) * (massP (u k - v) + dirichletP (u k - v)) := by
        intro k
        rw [hval k]
        have hb := hCbound (u k - v)
        have hb' : α * td.bd (u k - v) (u k - v)
            ≤ α * C * (dirichletP (u k - v) + massP (u k - v)) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hb hα
        have hexpand : (1 + α * C) * (massP (u k - v) + dirichletP (u k - v))
            = massP (u k - v) + dirichletP (u k - v)
              + α * C * (dirichletP (u k - v) + massP (u k - v)) := by ring
        linarith [hb', hexpand]
      have hlower : ∀ k, 0 ≤
          (dirichletBilinPQ hΩ + α • bdQ td.bd td.vanishesOnNullAEP)
              (w k - Submodule.Quotient.mk v) (w k - Submodule.Quotient.mk v)
            + massBilinPQ (w k - Submodule.Quotient.mk v) (w k - Submodule.Quotient.mk v) := by
        intro k
        rw [hval k]
        have := mul_nonneg hα (td.bd_nonneg (u k - v))
        linarith [dirichletP_nonneg (u k - v), massP_nonneg (u k - v)]
      have hg0 : Tendsto (fun k => (1 + α * C) * (massP (u k - v) + dirichletP (u k - v)))
          atTop (𝓝 0) := by
        have h0 : Tendsto (fun k => massP (u k - v) + dirichletP (u k - v)) atTop (𝓝 0) := hv
        simpa using h0.const_mul (1 + α * C)
      exact squeeze_zero hlower hupper hg0
    compact := by
      intro w hw
      obtain ⟨M, hM⟩ := hw
      choose u hu using
        fun k => Submodule.Quotient.mk_surjective (nullAEP (thinDomain Cm Cp L R)) (w k)
      have hbound : ∀ k, dirichletP (u k) + massP (u k) ≤ M := by
        intro k
        have he := hM k
        rw [← hu k] at he
        simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, dirichletBilinPQ_mk,
          bdQ_mk, massBilinPQ_mk, dirichletBilinP_self, massBilinP_self] at he
        linarith [mul_nonneg hα (td.bd_nonneg (u k))]
      obtain ⟨ν, v, hνmono, hvMemLp, hvTendsto⟩ := hrel u ⟨M, hbound⟩
      refine ⟨ν, hνmono, ?_⟩
      intro η hη
      have hη4 : (0 : ℝ) < η / 4 := by linarith
      obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp ((tendsto_order.mp hvTendsto).2 (η / 4) hη4)
      refine ⟨K, fun k l hk hl => ?_⟩
      rw [show w (ν k) - w (ν l) = Submodule.Quotient.mk (u (ν k) - u (ν l)) by
        rw [← hu (ν k), ← hu (ν l), Submodule.Quotient.mk_sub]]
      simp only [massBilinPQ_mk, massBilinP_self]
      have ha : MemLp (u (ν k)).toFun 2 (volume.restrict (thinDomain Cm Cp L R)) :=
        (u (ν k)).memL2
      have hc : MemLp (u (ν l)).toFun 2 (volume.restrict (thinDomain Cm Cp L R)) :=
        (u (ν l)).memL2
      have hpt : ∀ p, ((u (ν k)).toFun p - (u (ν l)).toFun p) ^ 2 ≤
          2 * ((u (ν k)).toFun p - v p) ^ 2 + 2 * ((u (ν l)).toFun p - v p) ^ 2 := by
        intro p
        nlinarith [sq_nonneg (((u (ν k)).toFun p - v p) + ((u (ν l)).toFun p - v p))]
      have hInt1 : Integrable (fun p => ((u (ν k)).toFun p - (u (ν l)).toFun p) ^ 2)
          (volume.restrict (thinDomain Cm Cp L R)) := (ha.sub hc).integrable_sq
      have hInt2a : Integrable (fun p => ((u (ν k)).toFun p - v p) ^ 2)
          (volume.restrict (thinDomain Cm Cp L R)) := (ha.sub hvMemLp).integrable_sq
      have hInt2b : Integrable (fun p => ((u (ν l)).toFun p - v p) ^ 2)
          (volume.restrict (thinDomain Cm Cp L R)) := (hc.sub hvMemLp).integrable_sq
      have hInt2 : Integrable (fun p => 2 * ((u (ν k)).toFun p - v p) ^ 2
          + 2 * ((u (ν l)).toFun p - v p) ^ 2) (volume.restrict (thinDomain Cm Cp L R)) :=
        (hInt2a.const_mul 2).add (hInt2b.const_mul 2)
      have heq : massP (u (ν k) - u (ν l))
          = ∫ p in thinDomain Cm Cp L R, ((u (ν k)).toFun p - (u (ν l)).toFun p) ^ 2 := by
        unfold massP
        simp only [H1P.sub_toFun, Pi.sub_apply]
      have hmono : massP (u (ν k) - u (ν l)) ≤
          2 * (∫ p in thinDomain Cm Cp L R, ((u (ν k)).toFun p - v p) ^ 2)
            + 2 * (∫ p in thinDomain Cm Cp L R, ((u (ν l)).toFun p - v p) ^ 2) := by
        rw [heq]
        calc ∫ p in thinDomain Cm Cp L R, ((u (ν k)).toFun p - (u (ν l)).toFun p) ^ 2
            ≤ ∫ p in thinDomain Cm Cp L R, (2 * ((u (ν k)).toFun p - v p) ^ 2
                + 2 * ((u (ν l)).toFun p - v p) ^ 2) := integral_mono hInt1 hInt2 hpt
          _ = 2 * (∫ p in thinDomain Cm Cp L R, ((u (ν k)).toFun p - v p) ^ 2)
              + 2 * (∫ p in thinDomain Cm Cp L R, ((u (ν l)).toFun p - v p) ^ 2) := by
              rw [integral_add (hInt2a.const_mul 2) (hInt2b.const_mul 2), integral_const_mul,
                integral_const_mul]
      have hk' := hK k hk
      have hl' := hK l hl
      linarith [hmono, hk', hl'] }

/-- Unfolding lemma for the energy field of `robinSetting_eth`. -/
theorem robinSetting_Q_eth (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (td : TraceData Cm Cp L R)
    {α : ℝ} (hα : 0 ≤ α) (hrel : RellichEmbeddingP (thinDomain Cm Cp L R))
    (hcomp : H1PCompleteProp (thinDomain Cm Cp L R)) :
    (robinSetting_eth hR hL td hα hrel hcomp).Q
      = dirichletBilinPQ (isOpen_thinDomain hR hL) + α • bdQ td.bd td.vanishesOnNullAEP := rfl

/-- Unfolding lemma for the mass field of `robinSetting_eth`. -/
theorem robinSetting_N_eth (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (td : TraceData Cm Cp L R)
    {α : ℝ} (hα : 0 ≤ α) (hrel : RellichEmbeddingP (thinDomain Cm Cp L R))
    (hcomp : H1PCompleteProp (thinDomain Cm Cp L R)) :
    (robinSetting_eth hR hL td hα hrel hcomp).N = massBilinPQ := rfl

/-! ## The min–max values of `robinSetting_eth` are `lambdaThin` -/

/-- **The abstract min–max values of `robinSetting_eth` are the manuscript's variational
Robin eigenvalues `lambdaThin`.** -/
theorem minmax_robinSetting_eth (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (td : TraceData Cm Cp L R) {α : ℝ} (hα : 0 ≤ α)
    (hrel : RellichEmbeddingP (thinDomain Cm Cp L R))
    (hcomp : H1PCompleteProp (thinDomain Cm Cp L R)) (j : ℕ) :
    RobinCaps.Spectrum.minmax (robinSetting_eth hR hL td hα hrel hcomp).q
        (robinSetting_eth hR hL td hα hrel hcomp).n j
      = lambdaThin hR hL td α j := by
  have hq : (robinSetting_eth hR hL td hα hrel hcomp).q
      = robinFormPQ (isOpen_thinDomain hR hL) td.bd td.vanishesOnNullAEP α := by
    funext x
    exact (robinFormPQ_eq_bilin (isOpen_thinDomain hR hL) td.bd td.vanishesOnNullAEP α x).symm
  have hn : (robinSetting_eth hR hL td hα hrel hcomp).n
      = massPQ (Ω := thinDomain Cm Cp L R) := by
    funext x; rfl
  rw [hq, hn]
  rfl

/-! ## The genuine Robin eigenfunctions of the thin domain -/

/-- **The genuine `H1P`-representative eigenfunctions of the thin-domain Robin problem.**

Given a `j`-dimensional subspace of `H1PQ (thinDomain Cm Cp L R)` (`hex`) and the abstract
eigenfunction theorem for `robinSetting_eth` (`heig`), there are representatives
`ψ 0, …, ψ (j-1) : H1P (thinDomain Cm Cp L R)` which are `massBilinP`-orthonormal, solve the
weak Robin eigenvalue equation with eigenvalue `lambdaThin hR hL td α (a+1)`, and whose
eigenvalues are nondecreasing. -/
theorem exists_eigenfunctions_eth (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (td : TraceData Cm Cp L R) {α : ℝ} (hα : 0 ≤ α)
    (hrel : RellichEmbeddingP (thinDomain Cm Cp L R))
    (hcomp : H1PCompleteProp (thinDomain Cm Cp L R)) (j : ℕ)
    (hex : ∃ V : Submodule ℝ (H1PQ (thinDomain Cm Cp L R)), Module.finrank ℝ V = j)
    (heig : RobinCaps.Spectrum.EigenFamilyProp (robinSetting_eth hR hL td hα hrel hcomp) j) :
    ∃ ψ : ℕ → H1P (thinDomain Cm Cp L R),
      (∀ a < j, ∀ b < j, massBilinP (ψ a) (ψ b) = if a = b then 1 else 0) ∧
      (∀ a < j, ∀ v : H1P (thinDomain Cm Cp L R),
        dirichletBilinP (ψ a) v + α * td.bd (ψ a) v
          = lambdaThin hR hL td α (a + 1) * massBilinP (ψ a) v) ∧
      (∀ a < j, ∀ b < j, a ≤ b →
        lambdaThin hR hL td α (a + 1) ≤ lambdaThin hR hL td α (b + 1)) := by
  obtain ⟨ψQ, μ, hortho, heigen, hmono, hval⟩ := heig hex
  choose ψ hψ using
    fun a => Submodule.Quotient.mk_surjective (nullAEP (thinDomain Cm Cp L R)) (ψQ a)
  have hμ : ∀ a, a < j → μ a = lambdaThin hR hL td α (a + 1) := by
    intro a ha
    rw [hval a ha, minmax_robinSetting_eth hR hL td hα hrel hcomp (a + 1)]
  refine ⟨ψ, ?_, ?_, ?_⟩
  · intro a ha b hb
    have h := hortho a ha b hb
    rw [robinSetting_N_eth, ← hψ a, ← hψ b, massBilinPQ_mk] at h
    exact h
  · intro a ha v
    have h := heigen a ha (Submodule.Quotient.mk v)
    rw [robinSetting_Q_eth, robinSetting_N_eth, ← hψ a] at h
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, dirichletBilinPQ_mk,
      bdQ_mk, massBilinPQ_mk] at h
    rw [hμ a ha] at h
    exact h
  · intro a ha b hb hab
    rw [← hμ a ha, ← hμ b hb]
    exact hmono a ha b hb hab

end RobinCaps.ThinDomain

end
