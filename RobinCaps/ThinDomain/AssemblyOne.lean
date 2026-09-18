import RobinCaps.ThinDomain.Assembly
import RobinCaps.ThinDomain.TrialAC
import RobinCaps.ThinDomain.TraceOne
import RobinCaps.ThinDomain.BdSliceableOne
import RobinCaps.Cap.Main

/-!
# The `m = 1` global comparison of `sec:proof`: bulk fields and final assembly

This file carries out, **against an interface**, the last step of the manuscript's proof of
`thm:main` in transverse dimension `m = 1`.

Work in progress in sibling files supplies three analytic bricks, recorded here as precisely
stated `Prop`s (Part A):

* `CapLowerInput_a1` — `lem:cap` (`eq:cap-lower`, `eq:cap-mass-bound`) in thin-domain scaling,
  for the two cap components of `u : H1P Ω_R`;
* `InterfaceTraceInput_a1` — `eq:interval-trace` / `eq:cap-rescale`: the entrance pairing
  `p_∓ = ⟨Tr_Σ U, Ψ_R⟩` is the endpoint value `F(x_∓)` of the axial profile
  (`RobinCaps/ThinDomain/InterfaceTrace.lean`);
* `TrialEnergyInput_a1` — `eq:trial-energy`, the `trial_energy` field of
  `GlobalComparisonData` (`RobinCaps/ThinDomain/TrialAssemblyOne.lean`);
* `TraceIneqInput_a1` — the planar trace inequality `TraceIneqOne` for every small radius
  (`RobinCaps/ThinDomain/TraceIneqStadium.lean`).

Everything else is **proved** here.
-/

open MeasureTheory Set Filter Metric

open scoped ENNReal Topology

noncomputable section

namespace RobinCaps.ThinDomain

open RobinCaps.Domain RobinCaps.Sobolev RobinCaps.Transverse RobinCaps.Cap

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-! ## Part 0: elementary measure-theoretic helpers -/

/-- Splitting a set integral over `Ioo a c` at an interior point. -/
theorem setIntegral_Ioo_split_a1 {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioo a c)) :
    ∫ x in Ioo a c, f x = (∫ x in Ioo a b, f x) + ∫ x in Ioo b c, f x := by
  have hsub : (Ioo a b ∪ Ioo b c : Set ℝ) ⊆ Ioo a c := by
    rintro x (hx | hx)
    · exact ⟨hx.1, lt_of_lt_of_le hx.2 hbc⟩
    · exact ⟨lt_of_le_of_lt hab hx.1, hx.2⟩
  have hdisj : Disjoint (Ioo a b) (Ioo b c) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx.2 (not_lt.2 hx'.1.le)
  have hae : Ioo a c =ᵐ[volume] (Ioo a b ∪ Ioo b c : Set ℝ) := by
    rw [ae_eq_set]
    refine ⟨measure_mono_null ?_ (measure_singleton b), ?_⟩
    · rintro x ⟨hx, hnx⟩
      simp only [mem_union, mem_Ioo, not_or, not_and, not_lt] at hnx
      have h1 : b ≤ x := hnx.1 hx.1
      rcases eq_or_lt_of_le h1 with h | h
      · exact h.symm
      · exact absurd (hnx.2 h) (not_le.2 hx.2)
    · rw [Set.diff_eq_empty.2 hsub, measure_empty]
  rw [setIntegral_congr_set hae,
    setIntegral_union hdisj measurableSet_Ioo
      (hf.mono_set (hsub.trans' Set.subset_union_left))
      (hf.mono_set (hsub.trans' Set.subset_union_right))]

/-- Translation of a set integral over an interval to the origin. -/
theorem setIntegral_Ioo_translate_a1 (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ) :
    ∫ x in Ioo a b, f (x - a) = ∫ y in Ioo 0 (b - a), f y := by
  rw [← Sobolev.intervalIntegral_eq_setIntegral_Ioo (f := fun x => f (x - a)) hab,
    ← Sobolev.intervalIntegral_eq_setIntegral_Ioo (f := f) (by linarith),
    intervalIntegral.integral_comp_sub_right (fun x => f x) a, sub_self]

/-! ## Part 1: the three axial pieces of the `m = 1` boundary form -/

section Pieces

variable {Cm Cp : Cap 1} {L R : ℝ}

/-- The axial density of the `m = 1` trace form (`RobinCaps.ThinDomain.traceForm_self_eq`). -/
def trDensOne_a1 (Cm Cp : Cap 1) (L R : ℝ) (u : H1P (thinDomain Cm Cp L R)) (x : ℝ) : ℝ :=
  areaElement Cm Cp L R x * (trPlus u x ^ 2 + trMinus u x ^ 2)

/-- The left-cap piece of the boundary form. -/
def bdCapL_a1 (Cm Cp : Cap 1) (L R : ℝ) (u : H1P (thinDomain Cm Cp L R)) : ℝ :=
  ∫ x in Ioo (-L / 2) (-L / 2 + Cm.K * R), trDensOne_a1 Cm Cp L R u x

/-- The bulk piece of the boundary form. -/
def bdBulk_a1 (Cm Cp : Cap 1) (L R : ℝ) (u : H1P (thinDomain Cm Cp L R)) : ℝ :=
  ∫ x in Ioo (-L / 2 + Cm.K * R) (L / 2 - Cp.K * R), trDensOne_a1 Cm Cp L R u x

/-- The right-cap piece of the boundary form. -/
def bdCapR_a1 (Cm Cp : Cap 1) (L R : ℝ) (u : H1P (thinDomain Cm Cp L R)) : ℝ :=
  ∫ x in Ioo (L / 2 - Cp.K * R) (L / 2), trDensOne_a1 Cm Cp L R u x

/-- **The boundary form of `Ω_R` splits into its three axial pieces.** -/
theorem traceForm_split_a1 (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (hti : TraceIneqOne Cm Cp L R) (u : H1P (thinDomain Cm Cp L R)) :
    traceForm hR hL u u
      = bdCapL_a1 Cm Cp L R u + bdBulk_a1 Cm Cp L R u + bdCapR_a1 Cm Cp L R u := by
  have h1 : -L / 2 ≤ -L / 2 + Cm.K * R := by nlinarith [Cm.hK, hR]
  have h2 : -L / 2 + Cm.K * R ≤ L / 2 - Cp.K * R := (interface_lt hR hL).le
  have h3 : L / 2 - Cp.K * R ≤ L / 2 := by nlinarith [Cp.hK, hR]
  have hf : IntegrableOn (trDensOne_a1 Cm Cp L R u) (Ioo (-L / 2) (L / 2)) volume :=
    hti.integrable u
  rw [traceForm_self_eq]
  show (∫ x in Ioo (-L / 2) (L / 2), trDensOne_a1 Cm Cp L R u x) = _
  rw [setIntegral_Ioo_split_a1 h1 (h2.trans h3) hf,
    setIntegral_Ioo_split_a1 h2 h3 (hf.mono_set (Ioo_subset_Ioo h1 le_rfl))]
  simp only [bdCapL_a1, bdBulk_a1, bdCapR_a1]
  ring

end Pieces

/-! ## Part 2: the bulk piece is the cylinder boundary form of `bdTr R` -/

section Bulk

variable {Cm Cp : Cap 1} {L R : ℝ}

/-- The bulk restriction of `RobinCaps/ThinDomain/Restrict.lean` and the one of
`RobinCaps/ThinDomain/BulkProj.lean` agree. -/
theorem restrictBulk_eq_restrictBulkP_a1 (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    restrictBulk hR hL u = restrictBulkP hR u := rfl

/-- **The bulk piece of the `m = 1` boundary form is `bdCyl (bdTr R)`** on the bulk cylinder:
the area element is `1` there, the profile is `R`, and the two endpoint traces of
`RobinCaps/ThinDomain/TraceOne.lean` are the endpoint traces of the transverse slice
(`traceDensity_bulk_eq`). -/
theorem bdBulk_eq_bdCyl_a1 (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    bdBulk_a1 Cm Cp L R u
      = bdCyl (bdTr R) (restrictBulkP hR u) (restrictBulkP hR u) := by
  have hsub : Ioo (-L / 2 + Cm.K * R) (L / 2 - Cp.K * R) ⊆ Ioo (-L / 2) (L / 2) :=
    Ioo_subset_Ioo (by nlinarith [Cm.hK, hR]) (by nlinarith [Cp.hK, hR])
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub (ae_sliceGood hR hL u),
    ae_isGoodSlice (restrictBulkP hR u), ae_restrict_mem measurableSet_Ioo]
    with x hg hgs hxb
  have hv : (slice (restrictBulkP hR u) x).toFun
      =ᵐ[volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 1)) R)] fun z => u.toFun (x, z) := by
    rw [slice_toFun hgs]
    exact Filter.EventuallyEq.rfl
  have h := traceDensity_bulk_eq hR hL hxb hg (slice (restrictBulkP hR u) x) hv
  show trDensOne_a1 Cm Cp L R u x = _
  rw [trDensOne_a1, ← h]
  ring

end Bulk

/-! ## Part 3: the axial profile as an element of `H¹(0, ℓ_R)` -/

section Axial

variable {Cm Cp : Cap 1} {L R α : ℝ}

/-- The `m = 1` transverse ground state `ψ_R` of `B_1(R)`. -/
def psiOne_a1 (α R : ℝ) (hα : 0 < α) (hR : 0 < R) : TransH1 1 R :=
  (groundStateOne α R hα hR).psi

theorem psiOne_normalized_a1 (hα : 0 < α) (hR : 0 < R) :
    ∫ z in transverseBall 1 R, (psiOne_a1 α R hα hR).toFun z ^ 2 = 1 :=
  psi_normalized_integral (groundStateOne α R hα hR)

theorem h1Congr_symm_toFun_a1 {ℓ ℓ' : ℝ} (e : ℓ = ℓ') (W : Sobolev.H1 ℓ') :
    ((h1Congr e).symm W).toFun = W.toFun := by
  subst e; rfl

theorem h1QCongr_symm_mk_a1 {ℓ ℓ' : ℝ} (e : ℓ = ℓ') (W : Sobolev.H1 ℓ') :
    (h1QCongr e).symm (Submodule.Quotient.mk W)
      = (Submodule.Quotient.mk ((h1Congr e).symm W) : Sobolev.H1Q ℓ) := by
  subst e; rfl

/-- **The absolutely continuous representative of the axial profile `F`** of
`eq:bulk-projection`, as an element of the concrete one-dimensional model on the bulk interval
`I_R` of length `ℓ_R = bulkLength Cm Cp L R`.  This is the representative of `bulkProjThin u`
(`bulkProjThin_mk_a1`), so `F(x_∓)` are its endpoint values. -/
def axialRepOne_a1 (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (hα : 0 < α)
    (u : H1P (thinDomain Cm Cp L R)) : Sobolev.H1 (bulkLength Cm Cp L R) :=
  (h1Congr (bulkLength_eq_sub (Cm := Cm) (Cp := Cp) (L := L) (R := R))).symm
    (bulkRepT (interface_lt hR hL) isOpen_transverseBall volume_transverseBall_ne_top
      (psiOne_a1 α R hα hR).memL2 (psiOne_normalized_a1 hα hR) (restrictBulkP hR u))

theorem axialRepOne_toFun_a1 (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (hα : 0 < α)
    (u : H1P (thinDomain Cm Cp L R)) :
    (axialRepOne_a1 hR hL hα u).toFun
      = (bulkRepT (interface_lt hR hL) isOpen_transverseBall volume_transverseBall_ne_top
          (psiOne_a1 α R hα hR).memL2 (psiOne_normalized_a1 hα hR)
          (restrictBulkP hR u)).toFun :=
  h1Congr_symm_toFun_a1 _ _

/-- **The bulk projection `π` of `RobinCaps/ThinDomain/BulkProj.lean`, computed.** -/
theorem bulkProjThin_mk_a1 (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (hα : 0 < α)
    (u : H1P (thinDomain Cm Cp L R)) :
    bulkProjThin hR hL (psiOne_a1 α R hα hR).memL2 (psiOne_normalized_a1 hα hR)
        (Submodule.Quotient.mk u)
      = Submodule.Quotient.mk (axialRepOne_a1 hR hL hα u) := by
  rw [bulkProjThin_eq hR hL (psiOne_a1 α R hα hR).memL2 (psiOne_normalized_a1 hα hR)]
  simp only [LinearMap.comp_apply, restrictBulkPQ_mk, bulkProjT_mk, LinearEquiv.coe_coe]
  rw [h1QCongr_symm_mk_a1]
  rfl

/-- **`M[F]` is the `L²` norm of the axial profile on the bulk cylinder.** -/
theorem mass_axialRepOne_a1 (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (hα : 0 < α)
    (u : H1P (thinDomain Cm Cp L R)) :
    Sobolev.mass (bulkLength Cm Cp L R) (axialRepOne_a1 hR hL hα u)
      = ∫ x in Ioo (-L / 2 + Cm.K * R) (L / 2 - Cp.K * R),
          axialProfile (groundStateOne α R hα hR) (restrictBulkP hR u) x ^ 2 := by
  set a : ℝ := -L / 2 + Cm.K * R with ha
  set b : ℝ := L / 2 - Cp.K * R with hb
  have hab : a < b := interface_lt hR hL
  set V := bulkRepT (interface_lt hR hL) isOpen_transverseBall volume_transverseBall_ne_top
    (psiOne_a1 α R hα hR).memL2 (psiOne_normalized_a1 hα hR) (restrictBulkP hR u) with hV
  have hℓ : (0 : ℝ) < bulkLength Cm Cp L R := trialAC_bulkLength_pos hL
  have hfun : (axialRepOne_a1 hR hL hα u).toFun = V.toFun := axialRepOne_toFun_a1 hR hL hα u
  have h1 : Sobolev.mass (bulkLength Cm Cp L R) (axialRepOne_a1 hR hL hα u)
      = ∫ x in Ioo 0 (bulkLength Cm Cp L R), V.toFun x ^ 2 := by
    rw [Sobolev.mass, Sobolev.intervalIntegral_eq_setIntegral_Ioo hℓ.le, hfun]
  have h2 : (∫ x in Ioo 0 (bulkLength Cm Cp L R), V.toFun x ^ 2)
      = ∫ x in Ioo 0 (b - a), V.toFun x ^ 2 := by
    rw [bulkLength_eq_sub (Cm := Cm) (Cp := Cp) (L := L) (R := R)]
  have h3 : (∫ x in Ioo a b, V.toFun (x - a) ^ 2) = ∫ y in Ioo 0 (b - a), V.toFun y ^ 2 :=
    setIntegral_Ioo_translate_a1 a b hab.le (fun y => V.toFun y ^ 2)
  have h4 : (∫ x in Ioo a b, V.toFun (x - a) ^ 2)
      = ∫ x in Ioo a b, axialProfile (groundStateOne α R hα hR) (restrictBulkP hR u) x ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [bulkRepT_ae (interface_lt hR hL) isOpen_transverseBall
      volume_transverseBall_ne_top (psiOne_a1 α R hα hR).memL2 (psiOne_normalized_a1 hα hR)
      (restrictBulkP hR u)] with x hx
    show V.toFun (x - a) ^ 2 = _
    rw [show V.toFun (x - a) = axialCoeff (transverseBall 1 R) (restrictBulkP hR u).toFun
        (psiOne_a1 α R hα hR).toFun x from hx]
    rfl
  rw [h1, h2, ← h3, h4]

/-- **`D[F]` is the axial Dirichlet energy of the profile on the bulk cylinder.** -/
theorem dirichlet_axialRepOne_a1 (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (hα : 0 < α)
    (u : H1P (thinDomain Cm Cp L R)) :
    Sobolev.dirichlet (bulkLength Cm Cp L R) (axialRepOne_a1 hR hL hα u)
      = ∫ x in Ioo (-L / 2 + Cm.K * R) (L / 2 - Cp.K * R),
          axialProfileDeriv (groundStateOne α R hα hR) (restrictBulkP hR u) x ^ 2 := by
  set a : ℝ := -L / 2 + Cm.K * R with ha
  set b : ℝ := L / 2 - Cp.K * R with hb
  have hab : a < b := interface_lt hR hL
  set V := bulkRepT (interface_lt hR hL) isOpen_transverseBall volume_transverseBall_ne_top
    (psiOne_a1 α R hα hR).memL2 (psiOne_normalized_a1 hα hR) (restrictBulkP hR u) with hV
  have hℓ : (0 : ℝ) < bulkLength Cm Cp L R := trialAC_bulkLength_pos hL
  have hfun : (axialRepOne_a1 hR hL hα u).toFun = V.toFun := axialRepOne_toFun_a1 hR hL hα u
  have h1 : Sobolev.dirichlet (bulkLength Cm Cp L R) (axialRepOne_a1 hR hL hα u)
      = ∫ x in Ioo 0 (bulkLength Cm Cp L R), deriv V.toFun x ^ 2 := by
    rw [Sobolev.dirichlet, Sobolev.intervalIntegral_eq_setIntegral_Ioo hℓ.le, hfun]
  have h2 : (∫ x in Ioo 0 (bulkLength Cm Cp L R), deriv V.toFun x ^ 2)
      = ∫ x in Ioo 0 (b - a), deriv V.toFun x ^ 2 := by
    rw [bulkLength_eq_sub (Cm := Cm) (Cp := Cp) (L := L) (R := R)]
  have h3 : (∫ x in Ioo a b, deriv V.toFun (x - a) ^ 2)
      = ∫ y in Ioo 0 (b - a), deriv V.toFun y ^ 2 :=
    setIntegral_Ioo_translate_a1 a b hab.le (fun y => deriv V.toFun y ^ 2)
  have h4 : (∫ x in Ioo a b, deriv V.toFun (x - a) ^ 2)
      = ∫ x in Ioo a b,
          axialProfileDeriv (groundStateOne α R hα hR) (restrictBulkP hR u) x ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [bulkRepT_deriv_ae (interface_lt hR hL) isOpen_transverseBall
      volume_transverseBall_ne_top (psiOne_a1 α R hα hR).memL2 (psiOne_normalized_a1 hα hR)
      (restrictBulkP hR u)] with x hx
    show deriv V.toFun (x - a) ^ 2 = _
    rw [show deriv V.toFun (x - a) = axialCoeff (transverseBall 1 R) (restrictBulkP hR u).gx
        (psiOne_a1 α R hα hR).toFun x from hx]
    rfl
  rw [h1, h2, ← h3, h4]

end Axial

/-! ## Part 4: the exact three-piece splitting of the renormalized energy -/

section Split

variable {Cm Cp : Cap 1} {L R α : ℝ}

theorem massP_eq_sum_P_a1 (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    massP u = massP (restrictLeft hR hL u) + massP (restrictBulkP hR u)
      + massP (restrictRight hR hL u) :=
  massP_eq_sum hR hL u

theorem dirichletP_eq_sum_P_a1 (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    dirichletP u = dirichletP (restrictLeft hR hL u) + dirichletP (restrictBulkP hR u)
      + dirichletP (restrictRight hR hL u) :=
  dirichletP_eq_sum hR hL u

/-- The renormalized energy of the left cap component. -/
def capEnergyL_a1 (α ν : ℝ) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) : ℝ :=
  dirichletP (restrictLeft hR hL u) + α * bdCapL_a1 Cm Cp L R u
    - ν * massP (restrictLeft hR hL u)

/-- The renormalized energy of the right cap component. -/
def capEnergyR_a1 (α ν : ℝ) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) : ℝ :=
  dirichletP (restrictRight hR hL u) + α * bdCapR_a1 Cm Cp L R u
    - ν * massP (restrictRight hR hL u)

/-- **The renormalized Robin energy of `Ω_R` splits exactly into the two cap energies and the
renormalized bulk energy** `E_bulk - ν N_bulk` of `RobinCaps/ThinDomain/BulkEnergy.lean`. -/
theorem energy_split_a1 (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (hti : TraceIneqOne Cm Cp L R) (ν : ℝ) (u : H1P (thinDomain Cm Cp L R)) :
    dirichletP u + α * traceForm hR hL u u - ν * massP u
      = capEnergyL_a1 α ν hR hL u
        + (EB α (bdTr R) (restrictBulkP hR u) - ν * massP (restrictBulkP hR u))
        + capEnergyR_a1 α ν hR hL u := by
  rw [capEnergyL_a1, capEnergyR_a1, EB, ← bdBulk_eq_bdCyl_a1 hR hL u,
    dirichletP_eq_sum_P_a1 hR hL u, massP_eq_sum_P_a1 hR hL u, traceForm_split_a1 hR hL hti u]
  ring

end Split

/-! ## Part A: the interface — the analytic bricks assumed from sibling files

The four `Prop`s of this section are exactly the statements that the in-progress files listed
in each docstring will discharge.  Nothing else about the caps, the interface trace or the
trial extension is used below. -/

section Interface

/-- **`lem:cap` in thin-domain scaling** (`eq:cap-lower`, `eq:cap-mass-bound`), for `m = 1`.

For every admissible radius there are two nonnegative functionals `G_∓[u] = ‖∇ g_∓‖²_{L²(C_∓)}`
(the squared cap gradients of the cap decomposition `eq:c-g-definition`) such that

* `E_cap^∓[u] ≥ (β_∓ − C R)|p_∓|² + (2R)^{-1} G_∓[u]`  (`eq:cap-lower`),
* `N_cap^∓[u] ≤ C R |p_∓|² + C R G_∓[u]`  (`eq:cap-mass-bound`),

where `E_cap^∓` is `capEnergyL_a1` / `capEnergyR_a1` (the cap part of the Robin form minus
`ν_R` times the cap mass, with the cap part of the boundary form of
`RobinCaps/ThinDomain/TraceOne.lean`), and where the entrance pairing
`p_∓ = ⟨Tr_Σ U, Ψ_R⟩` of `eq:cap-rescale` is written, using `eq:interval-trace`
(`InterfaceTraceInput_a1` below), as the endpoint value `F(x_∓)` of the axial profile,
i.e. as the value of `axialRepOne_a1` at `0` resp. at `ℓ_R`.

To be discharged by `RobinCaps/ThinDomain/CapLowerOne.lean` (the `m = 1` instance of
`RobinCaps.Cap.cap_lower_c1`, `RobinCaps/Cap/EnergyC1.lean`) together with
`RobinCaps/ThinDomain/InterfaceTrace.lean`. -/
structure CapLowerInput_a1 (Cm Cp : Cap 1) (L α : ℝ) (hα : 0 < α) (Ccap R₀ : ℝ) : Prop where
  /-- For every admissible `R` the two cap decompositions of `lem:cap` exist. -/
  cap : ∀ (R : ℝ) (hR : 0 < R), R < R₀ → ∀ hL : (Cm.K + Cp.K) * R < L,
    ∃ Gm Gp : H1P (thinDomain Cm Cp L R) → ℝ,
      (∀ u, 0 ≤ Gm u) ∧ (∀ u, 0 ≤ Gp u) ∧
      (∀ u, (Cm.beta α - Ccap * R) * (axialRepOne_a1 hR hL hα u).toFun 0 ^ 2
              + (2 * R)⁻¹ * Gm u
            ≤ capEnergyL_a1 α (nuR α R hα hR) hR hL u) ∧
      (∀ u, (Cp.beta α - Ccap * R)
                * (axialRepOne_a1 hR hL hα u).toFun (bulkLength Cm Cp L R) ^ 2
              + (2 * R)⁻¹ * Gp u
            ≤ capEnergyR_a1 α (nuR α R hα hR) hR hL u) ∧
      (∀ u, massP (restrictLeft hR hL u)
            ≤ Ccap * R * (axialRepOne_a1 hR hL hα u).toFun 0 ^ 2 + Ccap * R * Gm u) ∧
      (∀ u, massP (restrictRight hR hL u)
            ≤ Ccap * R * (axialRepOne_a1 hR hL hα u).toFun (bulkLength Cm Cp L R) ^ 2
                + Ccap * R * Gp u)

/-- **`eq:interval-trace` / `eq:cap-rescale`: the entrance pairing is the endpoint value of the
axial profile.**

For every `u ∈ H¹(Ω_R)` there are interface values `f_∓ ∈ L²(B_1(R))` — the traces of `u` on the
two interface disks `{x_∓} × B_1(R)` — with

* `F(x_∓) = ⟨f_∓, Ψ_R⟩_{L²(B_1(R))}` (this is the identification `p_∓ = F(x_∓)` that makes
  `CapLowerInput_a1` meaningful), and
* `∫_{B_1(R)} |f_∓|² ≤ C_ℓ (N_bulk[u] + ∫_{bulk} |∂_x u|²)` — the `H¹(I_R; L²(B))` endpoint
  trace bound of `eq:bulk-projection`.

To be discharged by `RobinCaps/ThinDomain/InterfaceTrace.lean`. -/
structure InterfaceTraceInput_a1 (Cm Cp : Cap 1) (L α : ℝ) (hα : 0 < α) (Cif R₀ : ℝ) : Prop where
  /-- The two interface values and their two properties. -/
  iface : ∀ (R : ℝ) (hR : 0 < R), R < R₀ → ∀ (hL : (Cm.K + Cp.K) * R < L)
      (u : H1P (thinDomain Cm Cp L R)),
    ∃ fm fp : EuclideanSpace ℝ (Fin 1) → ℝ,
      MemLp fm 2 (volume.restrict (transverseBall 1 R)) ∧
      MemLp fp 2 (volume.restrict (transverseBall 1 R)) ∧
      (axialRepOne_a1 hR hL hα u).toFun 0
        = ∫ z in transverseBall 1 R, fm z * (psiOne_a1 α R hα hR).toFun z ∧
      (axialRepOne_a1 hR hL hα u).toFun (bulkLength Cm Cp L R)
        = ∫ z in transverseBall 1 R, fp z * (psiOne_a1 α R hα hR).toFun z ∧
      (∫ z in transverseBall 1 R, fm z ^ 2)
        ≤ Cif * (massP (restrictBulkP hR u) + axialDirichletP (restrictBulkP hR u)) ∧
      (∫ z in transverseBall 1 R, fp z ^ 2)
        ≤ Cif * (massP (restrictBulkP hR u) + axialDirichletP (restrictBulkP hR u))

/-- **The planar trace inequality of `RobinCaps/ThinDomain/TraceOne.lean` for every small
radius.**  This is what turns `traceDataOne` into a `TraceFamily`.

To be discharged by `RobinCaps/ThinDomain/TraceIneqStadium.lean`. -/
structure TraceIneqInput_a1 (Cm Cp : Cap 1) (L R₀ : ℝ) : Prop where
  /-- `TraceIneqOne` holds at every admissible radius. -/
  ineq : ∀ R : ℝ, 0 < R → R < R₀ → TraceIneqOne Cm Cp L R

/-- **`eq:trial-energy`**: the `trial_energy` field of
`RobinCaps.ThinDomain.GlobalComparisonData`, for the trial extension
`liftQ` of `RobinCaps/ThinDomain/TrialAC.lean` with the `m = 1` transverse ground state.

To be discharged by `RobinCaps/ThinDomain/TrialAssemblyOne.lean`. -/
structure TrialEnergyInput_a1 (Cm Cp : Cap 1) (L α : ℝ) (hα : 0 < α)
    (hm0 : Cm.θ 0 = 0) (hp0 : Cp.θ 0 = 0) (Ctr R₀ : ℝ) : Prop where
  /-- `E_R[T_R F] ≤ a_{β₋+CR, β₊+CR; I_R}[F]`. -/
  trial : ∀ (R : ℝ) (hR : 0 < R), R < R₀ → ∀ (hL : (Cm.K + Cp.K) * R < L)
      (hti : TraceIneqOne Cm Cp L R) (v : Sobolev.H1Q (bulkLength Cm Cp L R)),
    robinFormPQ (isOpen_thinDomain hR hL) (traceDataOne hR hL hm0 hp0 hti).bd
          (traceDataOne hR hL hm0 hp0 hti).vanishesOnNullAEP α
          (liftQ hR hL (psiOne_a1 α R hα hR) v)
        - nuR α R hα hR * massPQ (liftQ hR hL (psiOne_a1 α R hα hR) v)
      ≤ robinFormQ (Cm.beta α + Ctr * R) (Cp.beta α + Ctr * R) (bulkLength Cm Cp L R) v

end Interface

/-! ## Part 5: `eq:Z-definition` and the two global bounds, at the level of representatives -/

section Estimates

variable {Cm Cp : Cap 1} {L R α : ℝ}

/-- **`eq:Z-definition`** `Z_R[u] = ‖w‖²_{L²(B_R)} + C₀ R Σ_σ ‖∇g_σ‖²_{L²(C_σ)}`, at the level
of representatives. -/
def Zrep_a1 (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (hα : 0 < α) (C₀ : ℝ)
    (Gm Gp : H1P (thinDomain Cm Cp L R) → ℝ) (u : H1P (thinDomain Cm Cp L R)) : ℝ :=
  massP (bulkRemainder (interface_lt hR hL) (groundStateOne α R hα hR) (restrictBulkP hR u))
    + C₀ * R * (Gm u + Gp u)

theorem Zrep_eq_a1 (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (hα : 0 < α) (C₀ : ℝ)
    (Gm Gp : H1P (thinDomain Cm Cp L R) → ℝ) (u : H1P (thinDomain Cm Cp L R)) :
    Zrep_a1 hR hL hα C₀ Gm Gp u
      = massP (bulkRemainder (interface_lt hR hL) (groundStateOne α R hα hR)
          (restrictBulkP hR u)) + C₀ * R * (Gm u + Gp u) := rfl

theorem Zrep_nonneg_a1 (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (hα : 0 < α) {C₀ : ℝ}
    (hC₀ : 0 ≤ C₀) {Gm Gp : H1P (thinDomain Cm Cp L R) → ℝ} (hGm : ∀ u, 0 ≤ Gm u)
    (hGp : ∀ u, 0 ≤ Gp u) (u : H1P (thinDomain Cm Cp L R)) :
    0 ≤ Zrep_a1 hR hL hα C₀ Gm Gp u := by
  have h1 : 0 ≤ massP (bulkRemainder (interface_lt hR hL) (groundStateOne α R hα hR)
      (restrictBulkP hR u)) := massP_nonneg _
  have h2 : 0 ≤ C₀ * R * (Gm u + Gp u) := by
    have h3 := hGm u
    have h4 := hGp u
    have h5 : (0 : ℝ) ≤ R := hR.le
    positivity
  rw [Zrep_eq_a1]
  linarith

/-- **`eq:global-energy-lower`, at the level of representatives.**

`E_R[u] ≥ a_R[F] + c₀ R^{-2} Z_R[u]`: the bulk contribution is `bulk_separation`
(`eq:exact-separation` + `eq:T-bound`), the two cap contributions are `eq:cap-lower`, and the
three pieces are glued by `energy_split_a1`. -/
theorem lower_rep_a1 (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (hα : 0 < α)
    (hti : TraceIneqOne Cm Cp L R)
    {Ccap C C₀ c₀ cgap : ℝ} {Gm Gp : H1P (thinDomain Cm Cp L R) → ℝ}
    (hGm : ∀ u, 0 ≤ Gm u) (hGp : ∀ u, 0 ≤ Gp u)
    (hcapL : ∀ u, (Cm.beta α - Ccap * R) * (axialRepOne_a1 hR hL hα u).toFun 0 ^ 2
        + (2 * R)⁻¹ * Gm u ≤ capEnergyL_a1 α (nuR α R hα hR) hR hL u)
    (hcapR : ∀ u, (Cp.beta α - Ccap * R)
          * (axialRepOne_a1 hR hL hα u).toFun (bulkLength Cm Cp L R) ^ 2
        + (2 * R)⁻¹ * Gp u ≤ capEnergyR_a1 α (nuR α R hα hR) hR hL u)
    (hgap : cgap ≤ (groundStateOne α R hα hR).gapConst)
    (hCC : Ccap ≤ C) (hc₀gap : c₀ ≤ cgap) (hc₀C₀ : c₀ * C₀ ≤ 1 / 2)
    (u : H1P (thinDomain Cm Cp L R)) :
    Sobolev.robinForm (Cm.beta α - C * R) (Cp.beta α - C * R) (bulkLength Cm Cp L R)
          (axialRepOne_a1 hR hL hα u)
        + c₀ / R ^ 2 * Zrep_a1 hR hL hα C₀ Gm Gp u
      ≤ dirichletP u + α * traceForm hR hL u u - nuR α R hα hR * massP u := by
  have hRne : R ≠ 0 := ne_of_gt hR
  have hR2 : (0 : ℝ) < R ^ 2 := by positivity
  have hZW0 : 0 ≤ massP (bulkRemainder (interface_lt hR hL) (groundStateOne α R hα hR)
      (restrictBulkP hR u)) := massP_nonneg _
  have hG : 0 ≤ Gm u + Gp u := by linarith [hGm u, hGp u]
  have hnu : (groundStateOne α R hα hR).nu = nuR α R hα hR := rfl
  have hD := dirichlet_axialRepOne_a1 hR hL hα u
  have hbulk := bulk_separation (interface_lt hR hL) (groundStateOne α R hα hR)
    (bdSliceable_bdTr hR (-L / 2 + Cm.K * R) (L / 2 - Cp.K * R)) (restrictBulkP hR u)
  rw [← hD, hnu] at hbulk
  have hsplit := energy_split_a1 (α := α) hR hL hti (nuR α R hα hR) u
  have hcl := hcapL u
  have hcr := hcapR u
  -- the two spectral absorptions
  have e1 : c₀ / R ^ 2 * massP (bulkRemainder (interface_lt hR hL) (groundStateOne α R hα hR)
        (restrictBulkP hR u))
      ≤ (groundStateOne α R hα hR).gapConst * R⁻¹ ^ 2
        * massP (bulkRemainder (interface_lt hR hL) (groundStateOne α R hα hR)
            (restrictBulkP hR u)) := by
    refine mul_le_mul_of_nonneg_right ?_ hZW0
    have hle : c₀ ≤ (groundStateOne α R hα hR).gapConst := le_trans hc₀gap hgap
    have hrw : c₀ / R ^ 2 = c₀ * (R ^ 2)⁻¹ := by ring
    rw [hrw, inv_pow]
    exact mul_le_mul_of_nonneg_right hle (by positivity)
  have hcoef : c₀ / R ^ 2 * (C₀ * R) ≤ (2 * R)⁻¹ := by
    have h1 : c₀ / R ^ 2 * (C₀ * R) = c₀ * C₀ * R⁻¹ := by field_simp
    have h2 : (2 * R)⁻¹ = 1 / 2 * R⁻¹ := by field_simp
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_right hc₀C₀ (by positivity)
  have e2 : c₀ / R ^ 2 * (C₀ * R * (Gm u + Gp u)) ≤ (2 * R)⁻¹ * (Gm u + Gp u) := by
    calc c₀ / R ^ 2 * (C₀ * R * (Gm u + Gp u))
        = c₀ / R ^ 2 * (C₀ * R) * (Gm u + Gp u) := by ring
      _ ≤ (2 * R)⁻¹ * (Gm u + Gp u) := mul_le_mul_of_nonneg_right hcoef hG
  -- weakening the two endpoint coefficients from `Ccap` to `C`
  have hendL : (Cm.beta α - C * R) * (axialRepOne_a1 hR hL hα u).toFun 0 ^ 2
      ≤ (Cm.beta α - Ccap * R) * (axialRepOne_a1 hR hL hα u).toFun 0 ^ 2 := by
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    nlinarith [hCC, hR.le]
  have hendR : (Cp.beta α - C * R)
        * (axialRepOne_a1 hR hL hα u).toFun (bulkLength Cm Cp L R) ^ 2
      ≤ (Cp.beta α - Ccap * R)
        * (axialRepOne_a1 hR hL hα u).toFun (bulkLength Cm Cp L R) ^ 2 := by
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    nlinarith [hCC, hR.le]
  rw [Sobolev.robinForm, Zrep_eq_a1, mul_add]
  linarith [hbulk, hcl, hcr, e1, e2, hendL, hendR, hsplit]

/-- **`eq:global-mass-upper`, at the level of representatives.**

`N_R[u] ≤ (1+CR) M[F] + CR D[F] + Z_R[u]`: the bulk mass splits exactly (`eq:bulk-mass`), the
two cap masses are `eq:cap-mass-bound`, and the entrance squares are absorbed by the interval
trace inequality `eq:interval-trace` (`RobinCaps.Sobolev.trace_ineq_uniform`). -/
theorem upper_rep_a1 (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (hα : 0 < α)
    {Ccap C C₀ Ctrace : ℝ} {Gm Gp : H1P (thinDomain Cm Cp L R) → ℝ}
    (hCcap : 0 ≤ Ccap) (hGm : ∀ u, 0 ≤ Gm u) (hGp : ∀ u, 0 ≤ Gp u)
    (hmassL : ∀ u, massP (restrictLeft hR hL u)
        ≤ Ccap * R * (axialRepOne_a1 hR hL hα u).toFun 0 ^ 2 + Ccap * R * Gm u)
    (hmassR : ∀ u, massP (restrictRight hR hL u)
        ≤ Ccap * R * (axialRepOne_a1 hR hL hα u).toFun (bulkLength Cm Cp L R) ^ 2
            + Ccap * R * Gp u)
    (htrace : ∀ v : Sobolev.H1 (bulkLength Cm Cp L R),
        v.toFun 0 ^ 2 + v.toFun (bulkLength Cm Cp L R) ^ 2
          ≤ Ctrace * (Sobolev.mass (bulkLength Cm Cp L R) v
              + Sobolev.dirichlet (bulkLength Cm Cp L R) v))
    (hCC : Ccap * Ctrace ≤ C) (hC₀ : Ccap ≤ C₀)
    (u : H1P (thinDomain Cm Cp L R)) :
    massP u
      ≤ (1 + C * R) * Sobolev.mass (bulkLength Cm Cp L R) (axialRepOne_a1 hR hL hα u)
        + C * R * Sobolev.dirichlet (bulkLength Cm Cp L R) (axialRepOne_a1 hR hL hα u)
        + Zrep_a1 hR hL hα C₀ Gm Gp u := by
  have hℓ : (0 : ℝ) < bulkLength Cm Cp L R := trialAC_bulkLength_pos hL
  have hMW : 0 ≤ Sobolev.mass (bulkLength Cm Cp L R) (axialRepOne_a1 hR hL hα u) :=
    Sobolev.mass_nonneg _ _ hℓ.le
  have hDW : 0 ≤ Sobolev.dirichlet (bulkLength Cm Cp L R) (axialRepOne_a1 hR hL hα u) :=
    Sobolev.dirichlet_nonneg _ _ hℓ.le
  have hsum := massP_eq_sum_P_a1 hR hL u
  have hM := mass_axialRepOne_a1 hR hL hα u
  have hbulkmass := bulk_mass_split (interface_lt hR hL) (groundStateOne α R hα hR)
    (restrictBulkP hR u)
  rw [← hM] at hbulkmass
  have hml := hmassL u
  have hmr := hmassR u
  have htr := htrace (axialRepOne_a1 hR hL hα u)
  have hGsum : 0 ≤ Gm u + Gp u := by linarith [hGm u, hGp u]
  have hRG : 0 ≤ R * (Gm u + Gp u) := mul_nonneg hR.le hGsum
  have habsG : Ccap * R * Gm u + Ccap * R * Gp u ≤ C₀ * R * (Gm u + Gp u) := by
    have h : 0 ≤ (C₀ - Ccap) * (R * (Gm u + Gp u)) := mul_nonneg (by linarith) hRG
    nlinarith [h]
  have hnn : 0 ≤ R * (Sobolev.mass (bulkLength Cm Cp L R) (axialRepOne_a1 hR hL hα u)
      + Sobolev.dirichlet (bulkLength Cm Cp L R) (axialRepOne_a1 hR hL hα u)) := by
    have hR' : (0 : ℝ) ≤ R := hR.le
    positivity
  have habs : Ccap * R * ((axialRepOne_a1 hR hL hα u).toFun 0 ^ 2
        + (axialRepOne_a1 hR hL hα u).toFun (bulkLength Cm Cp L R) ^ 2)
      ≤ C * R * (Sobolev.mass (bulkLength Cm Cp L R) (axialRepOne_a1 hR hL hα u)
          + Sobolev.dirichlet (bulkLength Cm Cp L R) (axialRepOne_a1 hR hL hα u)) := by
    have h1 : Ccap * R * ((axialRepOne_a1 hR hL hα u).toFun 0 ^ 2
          + (axialRepOne_a1 hR hL hα u).toFun (bulkLength Cm Cp L R) ^ 2)
        ≤ Ccap * R * (Ctrace * (Sobolev.mass (bulkLength Cm Cp L R) (axialRepOne_a1 hR hL hα u)
            + Sobolev.dirichlet (bulkLength Cm Cp L R) (axialRepOne_a1 hR hL hα u))) :=
      mul_le_mul_of_nonneg_left htr (mul_nonneg hCcap hR.le)
    have h2 : 0 ≤ (C - Ccap * Ctrace) * (R
        * (Sobolev.mass (bulkLength Cm Cp L R) (axialRepOne_a1 hR hL hα u)
          + Sobolev.dirichlet (bulkLength Cm Cp L R) (axialRepOne_a1 hR hL hα u))) :=
      mul_nonneg (by linarith) hnn
    nlinarith [h1, h2]
  rw [Zrep_eq_a1]
  linarith [hsum, hbulkmass, hml, hmr, habs, habsG]

end Estimates

/-! ## Part 6: the `GlobalComparisonData` instance at one radius -/

section Data

variable {Cm Cp : Cap 1} {L R α : ℝ}

/-- A chosen representative of a class in the a.e. quotient. -/
def qrep_a1 {m : ℕ} {Ω : Set (CapSpace m)} (w : H1PQ Ω) : H1P Ω :=
  Classical.choose (Submodule.Quotient.mk_surjective (nullAEP Ω) w)

theorem qrep_mk_a1 {m : ℕ} {Ω : Set (CapSpace m)} (w : H1PQ Ω) :
    (Submodule.Quotient.mk (qrep_a1 w) : H1PQ Ω) = w :=
  Classical.choose_spec (Submodule.Quotient.mk_surjective (nullAEP Ω) w)

/-- `eq:Z-definition` on the a.e. quotient, through the chosen representative. -/
def Zone_a1 (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (hα : 0 < α) (C₀ : ℝ)
    (Gm Gp : H1P (thinDomain Cm Cp L R) → ℝ) (w : H1PQ (thinDomain Cm Cp L R)) : ℝ :=
  Zrep_a1 hR hL hα C₀ Gm Gp (qrep_a1 w)

theorem Zone_eq_a1 (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (hα : 0 < α) (C₀ : ℝ)
    (Gm Gp : H1P (thinDomain Cm Cp L R) → ℝ) (w : H1PQ (thinDomain Cm Cp L R)) :
    Zone_a1 hR hL hα C₀ Gm Gp w = Zrep_a1 hR hL hα C₀ Gm Gp (qrep_a1 w) := rfl

/-- **The bulk/cap decomposition data of `sec:proof` at one radius, for `m = 1`.** -/
theorem globalComparisonData_one_a1 (hα : 0 < α) (hm0 : Cm.θ 0 = 0) (hp0 : Cp.θ 0 = 0)
    (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (hti : TraceIneqOne Cm Cp L R)
    {Ccap C C₀ c₀ cgap Ctrace Ctr : ℝ} {Gm Gp : H1P (thinDomain Cm Cp L R) → ℝ}
    (hCcap : 0 ≤ Ccap) (hC₀0 : 0 ≤ C₀)
    (hgap : cgap ≤ (groundStateOne α R hα hR).gapConst)
    (hCC : Ccap ≤ C) (hCCt : Ccap * Ctrace ≤ C) (hCtrC : Ctr ≤ C) (hC₀ : Ccap ≤ C₀)
    (hc₀gap : c₀ ≤ cgap) (hc₀C₀ : c₀ * C₀ ≤ 1 / 2)
    (htrace : ∀ v : Sobolev.H1 (bulkLength Cm Cp L R),
        v.toFun 0 ^ 2 + v.toFun (bulkLength Cm Cp L R) ^ 2
          ≤ Ctrace * (Sobolev.mass (bulkLength Cm Cp L R) v
              + Sobolev.dirichlet (bulkLength Cm Cp L R) v))
    (hGm : ∀ u, 0 ≤ Gm u) (hGp : ∀ u, 0 ≤ Gp u)
    (hcapL : ∀ u, (Cm.beta α - Ccap * R) * (axialRepOne_a1 hR hL hα u).toFun 0 ^ 2
        + (2 * R)⁻¹ * Gm u ≤ capEnergyL_a1 α (nuR α R hα hR) hR hL u)
    (hcapR : ∀ u, (Cp.beta α - Ccap * R)
          * (axialRepOne_a1 hR hL hα u).toFun (bulkLength Cm Cp L R) ^ 2
        + (2 * R)⁻¹ * Gp u ≤ capEnergyR_a1 α (nuR α R hα hR) hR hL u)
    (hmassL : ∀ u, massP (restrictLeft hR hL u)
        ≤ Ccap * R * (axialRepOne_a1 hR hL hα u).toFun 0 ^ 2 + Ccap * R * Gm u)
    (hmassR : ∀ u, massP (restrictRight hR hL u)
        ≤ Ccap * R * (axialRepOne_a1 hR hL hα u).toFun (bulkLength Cm Cp L R) ^ 2
            + Ccap * R * Gp u)
    (htrial : ∀ v : Sobolev.H1Q (bulkLength Cm Cp L R),
        robinFormPQ (isOpen_thinDomain hR hL) (traceDataOne hR hL hm0 hp0 hti).bd
              (traceDataOne hR hL hm0 hp0 hti).vanishesOnNullAEP α
              (liftQ hR hL (psiOne_a1 α R hα hR) v)
            - nuR α R hα hR * massPQ (liftQ hR hL (psiOne_a1 α R hα hR) v)
          ≤ robinFormQ (Cm.beta α + Ctr * R) (Cp.beta α + Ctr * R) (bulkLength Cm Cp L R) v) :
    Nonempty (GlobalComparisonData Cm Cp L α hR hL (traceDataOne hR hL hm0 hp0 hti)
      (nuR α R hα hR) C c₀) := by
  refine ⟨{
    π := bulkProjThin hR hL (psiOne_a1 α R hα hR).memL2 (psiOne_normalized_a1 hα hR)
    π_surj := bulkProjThin_surjective_trialAC hR hL (psiOne_a1 α R hα hR)
      (psiOne_normalized_a1 hα hR)
    Z := Zone_a1 hR hL hα C₀ Gm Gp
    Z_nonneg := fun w => Zrep_nonneg_a1 hR hL hα hC₀0 hGm hGp (qrep_a1 w)
    lift := liftQ hR hL (psiOne_a1 α R hα hR)
    trial_mass := massQ_le_massPQ_liftQ hR hL (psiOne_a1 α R hα hR)
      (groundStateOne α R hα hR).normalized
    lower := ?_
    upper := ?_
    trial_energy := ?_ }⟩
  · intro w
    have hw : (Submodule.Quotient.mk (qrep_a1 w) : H1PQ (thinDomain Cm Cp L R)) = w :=
      qrep_mk_a1 w
    have hpi := bulkProjThin_mk_a1 hR hL hα (qrep_a1 w)
    rw [hw] at hpi
    have hq := robinFormPQ_mk (isOpen_thinDomain hR hL) (traceDataOne hR hL hm0 hp0 hti).bd
      (traceDataOne hR hL hm0 hp0 hti).vanishesOnNullAEP α (qrep_a1 w)
    rw [hw] at hq
    have hm := massPQ_mk (qrep_a1 w)
    rw [hw] at hm
    have hbd : (traceDataOne hR hL hm0 hp0 hti).bd (qrep_a1 w) (qrep_a1 w)
        = traceForm hR hL (qrep_a1 w) (qrep_a1 w) := rfl
    rw [hpi, Sobolev.robinFormQ_mk, hq, hm, hbd, Zone_eq_a1]
    exact lower_rep_a1 hR hL hα hti hGm hGp hcapL hcapR hgap hCC hc₀gap hc₀C₀ (qrep_a1 w)
  · intro w
    have hw : (Submodule.Quotient.mk (qrep_a1 w) : H1PQ (thinDomain Cm Cp L R)) = w :=
      qrep_mk_a1 w
    have hpi := bulkProjThin_mk_a1 hR hL hα (qrep_a1 w)
    rw [hw] at hpi
    have hm := massPQ_mk (qrep_a1 w)
    rw [hw] at hm
    have hrf : Sobolev.robinForm 0 0 (bulkLength Cm Cp L R) (axialRepOne_a1 hR hL hα (qrep_a1 w))
        = Sobolev.dirichlet (bulkLength Cm Cp L R) (axialRepOne_a1 hR hL hα (qrep_a1 w)) := by
      rw [Sobolev.robinForm]; ring
    rw [hpi, Sobolev.massQ_mk, Sobolev.robinFormQ_mk, hrf, hm, Zone_eq_a1]
    exact upper_rep_a1 hR hL hα hCcap hGm hGp hmassL hmassR htrace hCCt hC₀ (qrep_a1 w)
  · intro v
    refine le_trans (htrial v) ?_
    refine Sobolev.robinFormQ_mono ?_ ?_ v <;> nlinarith [hCtrC, hR.le]

end Data

/-! ## Part 7: the trace family, `GlobalComparison`, `thm:main` and `cor:counterexample` -/

section Final

-- `hif` (`InterfaceTraceInput_a1`) is a *recorded* interface hypothesis: it is the statement
-- that justifies writing the entrance pairing `p_∓` of `CapLowerInput_a1` as `F(x_∓)`, and is
-- therefore carried in the signatures below even though the assembly itself only uses
-- `CapLowerInput_a1` in that already-translated form.
set_option linter.unusedVariables false

/-- **The recorded trace family for `m = 1`**, built from `traceDataOne` and the planar trace
inequality of `TraceIneqInput_a1`. -/
def traceFamilyOne_a1 (Cm Cp : Cap 1) (L R₀ : ℝ) (hm0 : Cm.θ 0 = 0) (hp0 : Cp.θ 0 = 0)
    (hR₀L : (Cm.K + Cp.K) * R₀ ≤ L) (hti : TraceIneqInput_a1 Cm Cp L R₀) :
    TraceFamily Cm Cp L R₀ :=
  fun R hR hRlt =>
    traceDataOne hR (lt_of_lt_of_le (by nlinarith [Cm.hK, Cp.hK, hRlt]) hR₀L) hm0 hp0
      (hti.ineq R hR hRlt)

/-- **The global comparison of `sec:proof` for `m = 1`.**

Everything is proved from the four interface `Prop`s of Part A; the constants are
`C = max (max C_cap (C_cap C_ℓ)) C_trial`, `C₀ = max C_cap 1`,
`c₀ = min c_gap (2C₀)^{-1}`, and the threshold is
`R₁ = min R₀ (min R_gap (L / (2(K₋+K₊))))`. -/
theorem globalComparison_one_a1 (Cm Cp : Cap 1) (L α : ℝ) (hL0 : 0 < L) (hα : 0 < α)
    (hm0 : Cm.θ 0 = 0) (hp0 : Cp.θ 0 = 0) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (hR₀L : (Cm.K + Cp.K) * R₀ ≤ L) {Ccap Cif Ctr : ℝ} (hCcap : 0 ≤ Ccap)
    (hti : TraceIneqInput_a1 Cm Cp L R₀)
    (hcap : CapLowerInput_a1 Cm Cp L α hα Ccap R₀)
    (hif : InterfaceTraceInput_a1 Cm Cp L α hα Cif R₀)
    (htr : TrialEnergyInput_a1 Cm Cp L α hα hm0 hp0 Ctr R₀) :
    GlobalComparison Cm Cp L α (nuOneDim α hα) R₀
      (traceFamilyOne_a1 Cm Cp L R₀ hm0 hp0 hR₀L hti) := by
  obtain ⟨Ctrace, hCtrace0, htraceu⟩ := Sobolev.trace_ineq_uniform L hL0
  obtain ⟨cgap, Rgap, hcgap, hRgap, hgapq⟩ := groundStateOne_gap_quant α hα
  have hKK : 0 < Cm.K + Cp.K := by linarith [Cm.hK, Cp.hK]
  set C₀ : ℝ := max Ccap 1 with hC₀def
  set C : ℝ := max (max Ccap (Ccap * Ctrace)) Ctr with hCdef
  set c₀ : ℝ := min cgap (1 / (2 * C₀)) with hc₀def
  set R₁ : ℝ := min R₀ (min Rgap (L / (2 * (Cm.K + Cp.K)))) with hR₁def
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hC₀0 : 0 ≤ C₀ := hC₀pos.le
  have hC₀le : Ccap ≤ C₀ := le_max_left _ _
  have hCC : Ccap ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCCt : Ccap * Ctrace ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCtrC : Ctr ≤ C := le_max_right _ _
  have hC0 : 0 ≤ C := le_trans hCcap hCC
  have hc₀pos : 0 < c₀ := lt_min hcgap (by positivity)
  have hc₀gap : c₀ ≤ cgap := min_le_left _ _
  have hc₀C₀ : c₀ * C₀ ≤ 1 / 2 := by
    have h1 : c₀ ≤ 1 / (2 * C₀) := min_le_right _ _
    have h2 : c₀ * C₀ ≤ 1 / (2 * C₀) * C₀ := mul_le_mul_of_nonneg_right h1 hC₀0
    have h3 : 1 / (2 * C₀) * C₀ = 1 / 2 := by field_simp
    linarith
  have hR₁pos : 0 < R₁ := lt_min hR₀ (lt_min hRgap (by positivity))
  have hR₁R₀ : R₁ ≤ R₀ := min_le_left _ _
  refine ⟨C, c₀, R₁, hC0, hc₀pos, hR₁pos, hR₁R₀, ?_⟩
  intro R hR hRR₀ hRR₁ hLR
  have hRRgap : R < Rgap :=
    lt_of_lt_of_le hRR₁ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hRKK : R < L / (2 * (Cm.K + Cp.K)) :=
    lt_of_lt_of_le hRR₁ (le_trans (min_le_right _ _) (min_le_right _ _))
  have hKKR : (Cm.K + Cp.K) * R < L / 2 := by
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * (Cm.K + Cp.K))] at hRKK
    linarith
  have hℓlow : L / 2 ≤ bulkLength Cm Cp L R := by
    simp only [Domain.bulkLength]; linarith
  have hℓhigh : bulkLength Cm Cp L R ≤ L := by
    simp only [Domain.bulkLength]
    nlinarith [hKK, hR.le]
  have htraceR : ∀ v : Sobolev.H1 (bulkLength Cm Cp L R),
      v.toFun 0 ^ 2 + v.toFun (bulkLength Cm Cp L R) ^ 2
        ≤ Ctrace * (Sobolev.mass (bulkLength Cm Cp L R) v
            + Sobolev.dirichlet (bulkLength Cm Cp L R) v) := by
    intro v
    simpa only [sq_abs] using htraceu (bulkLength Cm Cp L R) hℓlow hℓhigh v
  obtain ⟨Gm, Gp, hGm, hGp, hcapL, hcapR, hmassL, hmassR⟩ := hcap.cap R hR hRR₀ hLR
  have htrialR := htr.trial R hR hRR₀ hLR (hti.ineq R hR hRR₀)
  rw [nuOneDim_eq α hα hR]
  exact globalComparisonData_one_a1 hα hm0 hp0 hR hLR (hti.ineq R hR hRR₀) hCcap hC₀0
    (hgapq R hR hRRgap) hCC hCCt hCtrC hC₀le hc₀gap hc₀C₀ htraceR hGm hGp hcapL hcapR
    hmassL hmassR htrialR

/-- **`thm:main` for `m = 1`** (manuscript, statement lines 222–250), for the genuine
variational Robin eigenvalues `λ_j(Ω_R;α) = lambdaThin …` of the planar thin domain, with
`ν_R = λ₁(B_1(R);α) = nuOneDim α hα R`. -/
theorem mainTheorem_one_a1 (Cm Cp : Cap 1) (L α : ℝ) (hL0 : 0 < L) (hα : 0 < α)
    (hβm : 0 < Cm.beta α) (hβp : 0 < Cp.beta α)
    (hm0 : Cm.θ 0 = 0) (hp0 : Cp.θ 0 = 0) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (hR₀L : (Cm.K + Cp.K) * R₀ ≤ L) {Ccap Cif Ctr : ℝ} (hCcap : 0 ≤ Ccap)
    (hti : TraceIneqInput_a1 Cm Cp L R₀)
    (hcap : CapLowerInput_a1 Cm Cp L α hα Ccap R₀)
    (hif : InterfaceTraceInput_a1 Cm Cp L α hα Cif R₀)
    (htr : TrialEnergyInput_a1 Cm Cp L α hα hm0 hp0 Ctr R₀) :
    MainTheorem 1 Cm Cp L α hL0 hβm hβp (nuOneDim α hα) R₀
      (traceFamilyOne_a1 Cm Cp L R₀ hm0 hp0 hR₀L hti) :=
  mainTheorem_of_globalComparison 1 Cm Cp L α hL0 hα.le hβm hβp (nuOneDim α hα) R₀ _
    (globalComparison_one_a1 Cm Cp L α hL0 hα hm0 hp0 R₀ hR₀ hR₀L hCcap hti hcap hif htr)

/-- The hemispherical cap closes up: `θ(0) = 0`. -/
theorem hemisphere_theta_zero_a1 (m : ℕ) : (hemisphere m).θ 0 = 0 := by
  show semi 1 0 = 0
  simp [semi]

/-- **`cor:counterexample` for `m = 1`** (`n = 2`): for the planar capsule with two
hemispherical caps, and granted the four interface `Prop`s, for all small `R`

`λ₂(Ω_R;α) − λ₁(Ω_R;α) ≤ G_α(L) − Δ/2 < G_α(L) = G_α(diam Ω_R)`. -/
theorem counterexample_one_a1 (L α : ℝ) (hL0 : 0 < L) (hα : 0 < α) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (hR₀L : ((hemisphere 1).K + (hemisphere 1).K) * R₀ ≤ L)
    {Ccap Cif Ctr : ℝ} (hCcap : 0 ≤ Ccap)
    (hti : TraceIneqInput_a1 (hemisphere 1) (hemisphere 1) L R₀)
    (hcap : CapLowerInput_a1 (hemisphere 1) (hemisphere 1) L α hα Ccap R₀)
    (hif : InterfaceTraceInput_a1 (hemisphere 1) (hemisphere 1) L α hα Cif R₀)
    (htr : TrialEnergyInput_a1 (hemisphere 1) (hemisphere 1) L α hα
      (hemisphere_theta_zero_a1 1) (hemisphere_theta_zero_a1 1) Ctr R₀) :
    ∃ R₁ : ℝ, 0 < R₁ ∧ ∀ (R : ℝ) (hR : 0 < R), R < R₁ → ∀ (h2R : 2 * R < L)
        (hR₀' : R < R₀),
      lambdaThin hR (hemisphere_hL h2R)
            (traceFamilyOne_a1 (hemisphere 1) (hemisphere 1) L R₀
              (hemisphere_theta_zero_a1 1) (hemisphere_theta_zero_a1 1) hR₀L hti R hR hR₀')
            α 2
          - lambdaThin hR (hemisphere_hL h2R)
            (traceFamilyOne_a1 (hemisphere 1) (hemisphere 1) L R₀
              (hemisphere_theta_zero_a1 1) (hemisphere_theta_zero_a1 1) hR₀L hti R hR hR₀')
            α 1
        ≤ Interval.gap L hL0 α - Delta 1 L hL0 α / 2 ∧
      lambdaThin hR (hemisphere_hL h2R)
            (traceFamilyOne_a1 (hemisphere 1) (hemisphere 1) L R₀
              (hemisphere_theta_zero_a1 1) (hemisphere_theta_zero_a1 1) hR₀L hti R hR hR₀')
            α 2
          - lambdaThin hR (hemisphere_hL h2R)
            (traceFamilyOne_a1 (hemisphere 1) (hemisphere 1) L R₀
              (hemisphere_theta_zero_a1 1) (hemisphere_theta_zero_a1 1) hR₀L hti R hR hR₀')
            α 1
        < Interval.gap L hL0 α ∧
      euclidDiam (thinDomain (hemisphere 1) (hemisphere 1) L R) = L :=
  counterexample_of_mainTheorem' 1 le_rfl L α hL0 hα (nuOneDim α hα) R₀ hR₀ _
    (mainTheorem_one_a1 (hemisphere 1) (hemisphere 1) L α hL0 hα
      (hemisphere_beta_pos 1 le_rfl hα) (hemisphere_beta_pos 1 le_rfl hα)
      (hemisphere_theta_zero_a1 1) (hemisphere_theta_zero_a1 1) R₀ hR₀ hR₀L hCcap
      hti hcap hif htr)

end Final

end RobinCaps.ThinDomain

end
