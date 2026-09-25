import RobinCaps.ThinDomain.SelfAdjointIface
import RobinCaps.ThinDomain.RobinSpectrumFinal

/-!
# The Robin Laplacian as an unbounded operator on `L²(Ω_R)`

This file packages the weak Robin realization of `-Δ` of `ThinDomain/RobinOperator.lean`
(the relation `IsRobinImage_rop td α u f` between `u : H1P Ω` and `f : CapSpace m → ℝ`) as a
genuine **partially defined linear operator** `robinOp_rlp : H →ₗ.[ℝ] H` on the Hilbert space

`H := L²(Ω_R) = Lp ℝ 2 (volume.restrict Ω_R)`

(mathlib `MeasureTheory.Lp`, with inner product `⟪f,g⟫ = ∫ f g`, `MeasureTheory.L2.inner_def`),
and proves it is symmetric, nonnegative and self-adjoint under the abstract hypotheses of
`ThinDomain/SelfAdjointIface.lean` (`SelfAdjointCriterionProp`, `RobinLaxMilgramProp`), with
eigenvalues exactly the variational values `lambdaThin` of `ThinDomain/RobinSpectrumFinal.lean`.

## Contents

* `robinH_rlp Cm Cp L R` — the Hilbert space `H = L²(Ω_R)`, an abbreviation for
  `Lp ℝ 2 (volume.restrict (thinDomain Cm Cp L R))`.
* `inner_eq_integral_rlp` — the inner product of `H` is `⟪f,g⟫ = ∫_Ω f g`.
* `robinDomain_rlp hR hL td α` — the domain of the Robin Laplacian, `{f | ∃ u : H1P Ω,
  u.toFun =ᵐ f ∧ ∃ g, IsRobinImage_rop td α u g}`, bundled as a submodule of `H`.
* `isRobinImage_congr_rlp` — **well-definedness of the weak image on `a.e.` classes**: if `u`,
  `u'` represent the same element of `H` and have weak Robin images `g`, `g'`, then `g =ᵐ g'`
  (via `u - u' ∈ nullAEP Ω`, `dirichletBilinP_eq_zero_left`, `td.vanishes_ae` and
  `isRobinImage_unique_rop`).
* `robinOp_rlp hR hL td α : H →ₗ.[ℝ] H` — the Robin Laplacian, with domain `robinDomain_rlp`
  and value the (well-defined, by the above) class of a weak image; `robinOp_apply_rlp`
  identifies its value on (the class of) `u.toFun` with (the class of) `g` whenever
  `IsRobinImage_rop td α u g`.
* `robinOp_symm_rlp` — **symmetry**: `⟪robinOp_rlp x, y⟫ = ⟪x, robinOp_rlp y⟫` for
  `x y` in the domain (`isRobinImage_symm_rop`).
* `robinOp_nonneg_rlp` — **nonnegativity**: `0 ≤ ⟪robinOp_rlp x, x⟫` for `α ≥ 0`
  (`isRobinImage_nonneg_rop`).
* `robinOp_add_one_surj_rlp` — **surjectivity of `robinOp_rlp + 1`**, from
  `RobinLaxMilgramProp td α` (weak solvability of `(-Δ+1)v = h`).
* `robinOp_isSelfAdjoint_rlp` — **self-adjointness** of `robinOp_rlp`, from the abstract
  criterion `SelfAdjointCriterionProp` applied to the three properties above.
* `robinOp_eigen_iff_rlp` — **the eigenvalues of `robinOp_rlp` are exactly the variational
  values** `lambdaThin hR hL td α (a+1)`, `a : ℕ` (`robinOperator_spectrum_final`).

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped InnerProductSpace RealInnerProductSpace
open RobinCaps.Domain RobinCaps.Cap

namespace RobinCaps.ThinDomain

variable {m : ℕ} {Cm Cp : Cap m} {L R : ℝ}

/-! ## The ambient Hilbert space -/

/-- **The Hilbert space `H = L²(Ω_R)`.** -/
abbrev robinH_rlp (Cm Cp : Cap m) (L R : ℝ) : Type :=
  Lp ℝ 2 (volume.restrict (thinDomain Cm Cp L R))

theorem real_inner_apply_rlp (x y : ℝ) : (inner ℝ x y : ℝ) = x * y := by
  simp [RCLike.inner_apply, mul_comm]

/-- **The inner product of `H` is the `L²` pairing `⟪f,g⟫ = ∫_Ω f g`.** -/
theorem inner_eq_integral_rlp (f g : robinH_rlp Cm Cp L R) :
    ⟪f, g⟫ = ∫ p in thinDomain Cm Cp L R, (f : CapSpace m → ℝ) p * (g : CapSpace m → ℝ) p := by
  rw [MeasureTheory.L2.inner_def]
  exact integral_congr_ae (.of_forall fun p => real_inner_apply_rlp (f p) (g p))

/-! ## The domain of the Robin Laplacian -/

/-- **The domain of the Robin Laplacian**, as a submodule of `H = L²(Ω_R)`: the classes of
`H1P Ω` elements admitting a weak Robin image. -/
def robinDomain_rlp (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (td : TraceData Cm Cp L R)
    (α : ℝ) : Submodule ℝ (robinH_rlp Cm Cp L R) where
  carrier := {f | ∃ u : H1P (thinDomain Cm Cp L R),
      u.toFun =ᵐ[volume.restrict (thinDomain Cm Cp L R)] (f : CapSpace m → ℝ) ∧
        ∃ g, IsRobinImage_rop td α u g}
  zero_mem' := ⟨0, by
      filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2)
        (μ := volume.restrict (thinDomain Cm Cp L R))] with p hp
      simpa using hp.symm, fun _ => 0, isRobinImage_zero_rop td α⟩
  add_mem' := by
    rintro f f' ⟨u, hu, g, hg⟩ ⟨u', hu', g', hg'⟩
    refine ⟨u + u', ?_, g + g', isRobinImage_add_rop hg hg'⟩
    rw [H1P.add_toFun]
    exact (hu.add hu').trans (Lp.coeFn_add f f').symm
  smul_mem' := by
    rintro c f ⟨u, hu, g, hg⟩
    refine ⟨c • u, ?_, c • g, isRobinImage_smul_rop c hg⟩
    rw [H1P.smul_toFun]
    exact (hu.fun_comp (c • ·)).trans (Lp.coeFn_smul c f).symm

theorem mem_robinDomain_rlp_iff (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (td : TraceData Cm Cp L R) (α : ℝ) (f : robinH_rlp Cm Cp L R) :
    f ∈ robinDomain_rlp hR hL td α ↔
      ∃ u : H1P (thinDomain Cm Cp L R),
        u.toFun =ᵐ[volume.restrict (thinDomain Cm Cp L R)] (f : CapSpace m → ℝ) ∧
          ∃ g, IsRobinImage_rop td α u g := Iff.rfl

/-! ## Well-definedness of the weak Robin image on `a.e.` classes -/

/-- **Well-definedness of the weak Robin image relation.** If `u`, `u'` are represented by
`a.e.`-equal functions and have weak Robin images `g`, `g'` respectively, then `g =ᵐ g'`. -/
theorem isRobinImage_congr_rlp (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (td : TraceData Cm Cp L R) (α : ℝ) {u u' : H1P (thinDomain Cm Cp L R)}
    (huu' : u.toFun =ᵐ[volume.restrict (thinDomain Cm Cp L R)] u'.toFun)
    {g g' : CapSpace m → ℝ} (hg : IsRobinImage_rop td α u g)
    (hg' : IsRobinImage_rop td α u' g') :
    g =ᵐ[volume.restrict (thinDomain Cm Cp L R)] g' := by
  have hmem : (u - u') ∈ nullAEP (thinDomain Cm Cp L R) := by
    show (u - u').toFun =ᵐ[volume.restrict (thinDomain Cm Cp L R)] 0
    rw [H1P.sub_toFun]
    filter_upwards [huu'] with p hp
    simp [hp]
  have h0 : IsRobinImage_rop td α (u - u') (fun _ => (0 : ℝ)) := by
    refine ⟨MemLp.zero, fun v => ?_⟩
    have h1 : dirichletBilinP (u - u') v = 0 :=
      dirichletBilinP_eq_zero_left (isOpen_thinDomain hR hL) hmem v
    have h2 : td.bd (u - u') v = 0 := td.vanishes_ae _ hmem v
    rw [h1, h2]; simp
  have heqU : u + (-1 : ℝ) • u' = u - u' := by rw [neg_one_smul, sub_eq_add_neg]
  have heqG : g + (-1 : ℝ) • g' = g - g' := by rw [neg_one_smul, sub_eq_add_neg]
  have hsub : IsRobinImage_rop td α (u - u') (g - g') := by
    rw [← heqU, ← heqG]
    exact isRobinImage_add_rop hg (isRobinImage_smul_rop (-1) hg')
  have hz := isRobinImage_unique_rop hR hL h0 hsub
  filter_upwards [hz] with p hp
  simp only [Pi.sub_apply] at hp
  linarith

/-- **Transport of a weak Robin image along an `a.e.`-equal image function.** -/
theorem isRobinImage_ae_congr_image_rlp {td : TraceData Cm Cp L R} {α : ℝ}
    {u : H1P (thinDomain Cm Cp L R)} {f f' : CapSpace m → ℝ}
    (hff' : f =ᵐ[volume.restrict (thinDomain Cm Cp L R)] f')
    (hf : IsRobinImage_rop td α u f) : IsRobinImage_rop td α u f' := by
  obtain ⟨hL2, heq⟩ := hf
  refine ⟨hL2.ae_eq hff', fun v => ?_⟩
  rw [heq v]
  exact integral_congr_ae (hff'.mono fun p hp => by simp [hp])

/-! ## The Robin operator, as a `LinearPMap` -/

theorem mem_robinDomain_rlp_of_isRobinImage_rlp (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (td : TraceData Cm Cp L R) (α : ℝ) {u : H1P (thinDomain Cm Cp L R)}
    {g : CapSpace m → ℝ} (hg : IsRobinImage_rop td α u g) :
    u.memL2.toLp u.toFun ∈ robinDomain_rlp hR hL td α :=
  ⟨u, (MemLp.coeFn_toLp u.memL2).symm, g, hg⟩

/-- A chosen `H1P Ω` representative of `(x : H)`, for `x` in the Robin domain. -/
noncomputable def robinRep_rlp (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (td : TraceData Cm Cp L R) (α : ℝ) (x : robinDomain_rlp hR hL td α) :
    H1P (thinDomain Cm Cp L R) :=
  ((mem_robinDomain_rlp_iff hR hL td α (x : robinH_rlp Cm Cp L R)).mp x.2).choose

theorem robinRep_rlp_toFun_ae (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (td : TraceData Cm Cp L R) (α : ℝ) (x : robinDomain_rlp hR hL td α) :
    (robinRep_rlp hR hL td α x).toFun =ᵐ[volume.restrict (thinDomain Cm Cp L R)]
      ((x : robinH_rlp Cm Cp L R) : CapSpace m → ℝ) :=
  ((mem_robinDomain_rlp_iff hR hL td α (x : robinH_rlp Cm Cp L R)).mp x.2).choose_spec.1

/-- A chosen weak Robin image of `robinRep_rlp x`, i.e. of (a representative of) `x`. -/
noncomputable def robinImg_rlp (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (td : TraceData Cm Cp L R) (α : ℝ) (x : robinDomain_rlp hR hL td α) : CapSpace m → ℝ :=
  (((mem_robinDomain_rlp_iff hR hL td α (x : robinH_rlp Cm Cp L R)).mp x.2).choose_spec.2).choose

theorem robinImg_rlp_isRobinImage (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (td : TraceData Cm Cp L R) (α : ℝ) (x : robinDomain_rlp hR hL td α) :
    IsRobinImage_rop td α (robinRep_rlp hR hL td α x) (robinImg_rlp hR hL td α x) :=
  (((mem_robinDomain_rlp_iff hR hL td α (x : robinH_rlp Cm Cp L R)).mp x.2).choose_spec.2).choose_spec

/-- **The value of the Robin operator**, as a function `robinDomain_rlp hR hL td α → H`
(not yet packaged as a linear map). -/
noncomputable def robinOpVal_rlp (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (td : TraceData Cm Cp L R) (α : ℝ) (x : robinDomain_rlp hR hL td α) :
    robinH_rlp Cm Cp L R :=
  (robinImg_rlp_isRobinImage hR hL td α x).1.toLp (robinImg_rlp hR hL td α x)

/-- **Characterization of `robinOpVal_rlp`**: it agrees with the class of any weak Robin image
of any `H1P Ω` representative of `x`, by `isRobinImage_congr_rlp`. -/
theorem robinOpVal_eq_rlp (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (td : TraceData Cm Cp L R)
    (α : ℝ) {x : robinDomain_rlp hR hL td α} {u : H1P (thinDomain Cm Cp L R)}
    (hu : u.toFun =ᵐ[volume.restrict (thinDomain Cm Cp L R)]
      ((x : robinH_rlp Cm Cp L R) : CapSpace m → ℝ))
    {g : CapSpace m → ℝ} (hg : IsRobinImage_rop td α u g) :
    robinOpVal_rlp hR hL td α x = hg.1.toLp g := by
  have hcongr : robinImg_rlp hR hL td α x =ᵐ[volume.restrict (thinDomain Cm Cp L R)] g :=
    isRobinImage_congr_rlp hR hL td α
      ((robinRep_rlp_toFun_ae hR hL td α x).trans hu.symm)
      (robinImg_rlp_isRobinImage hR hL td α x) hg
  show (robinImg_rlp_isRobinImage hR hL td α x).1.toLp (robinImg_rlp hR hL td α x) = hg.1.toLp g
  exact (robinImg_rlp_isRobinImage hR hL td α x).1.toLp_congr hg.1 hcongr

theorem robinOpVal_add_rlp (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (td : TraceData Cm Cp L R)
    (α : ℝ) (x y : robinDomain_rlp hR hL td α) :
    robinOpVal_rlp hR hL td α (x + y) =
      robinOpVal_rlp hR hL td α x + robinOpVal_rlp hR hL td α y := by
  have hux := robinRep_rlp_toFun_ae hR hL td α x
  have hvy := robinRep_rlp_toFun_ae hR hL td α y
  have hgx := robinImg_rlp_isRobinImage hR hL td α x
  have hgy := robinImg_rlp_isRobinImage hR hL td α y
  have hxy : (robinRep_rlp hR hL td α x + robinRep_rlp hR hL td α y).toFun
      =ᵐ[volume.restrict (thinDomain Cm Cp L R)]
      (((x + y : robinDomain_rlp hR hL td α) : robinH_rlp Cm Cp L R) : CapSpace m → ℝ) := by
    rw [H1P.add_toFun]
    have hco : (((x + y : robinDomain_rlp hR hL td α) : robinH_rlp Cm Cp L R))
        = (x : robinH_rlp Cm Cp L R) + (y : robinH_rlp Cm Cp L R) := rfl
    rw [hco]
    exact (hux.add hvy).trans (Lp.coeFn_add _ _).symm
  have himg : IsRobinImage_rop td α (robinRep_rlp hR hL td α x + robinRep_rlp hR hL td α y)
      (robinImg_rlp hR hL td α x + robinImg_rlp hR hL td α y) :=
    isRobinImage_add_rop hgx hgy
  rw [robinOpVal_eq_rlp hR hL td α hxy himg]
  exact MemLp.toLp_add hgx.1 hgy.1

theorem robinOpVal_smul_rlp (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (td : TraceData Cm Cp L R)
    (α : ℝ) (c : ℝ) (x : robinDomain_rlp hR hL td α) :
    robinOpVal_rlp hR hL td α (c • x) = c • robinOpVal_rlp hR hL td α x := by
  have hux := robinRep_rlp_toFun_ae hR hL td α x
  have hgx := robinImg_rlp_isRobinImage hR hL td α x
  have hcx : (c • robinRep_rlp hR hL td α x).toFun
      =ᵐ[volume.restrict (thinDomain Cm Cp L R)]
      (((c • x : robinDomain_rlp hR hL td α) : robinH_rlp Cm Cp L R) : CapSpace m → ℝ) := by
    rw [H1P.smul_toFun]
    have hco : (((c • x : robinDomain_rlp hR hL td α) : robinH_rlp Cm Cp L R))
        = c • (x : robinH_rlp Cm Cp L R) := rfl
    rw [hco]
    exact (hux.fun_comp (c • ·)).trans (Lp.coeFn_smul c _).symm
  have himg : IsRobinImage_rop td α (c • robinRep_rlp hR hL td α x)
      (c • robinImg_rlp hR hL td α x) := isRobinImage_smul_rop c hgx
  rw [robinOpVal_eq_rlp hR hL td α hcx himg]
  exact MemLp.toLp_const_smul c hgx.1

/-- **The Robin Laplacian**, as a partially defined linear operator on `H = L²(Ω_R)`, with
domain `robinDomain_rlp`. -/
def robinOp_rlp (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (td : TraceData Cm Cp L R) (α : ℝ) :
    robinH_rlp Cm Cp L R →ₗ.[ℝ] robinH_rlp Cm Cp L R :=
  ⟨robinDomain_rlp hR hL td α,
    { toFun := robinOpVal_rlp hR hL td α
      map_add' := robinOpVal_add_rlp hR hL td α
      map_smul' := robinOpVal_smul_rlp hR hL td α }⟩

/-- **`robinOp_rlp` maps (the class of) `u.toFun` to (the class of) any weak Robin image
`g` of `u`.** -/
theorem robinOp_apply_rlp (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (td : TraceData Cm Cp L R)
    (α : ℝ) {u : H1P (thinDomain Cm Cp L R)} {g : CapSpace m → ℝ}
    (hg : IsRobinImage_rop td α u g) :
    robinOp_rlp hR hL td α
        ⟨u.memL2.toLp u.toFun, mem_robinDomain_rlp_of_isRobinImage_rlp hR hL td α hg⟩
      = hg.1.toLp g := by
  show robinOpVal_rlp hR hL td α
      ⟨u.memL2.toLp u.toFun, mem_robinDomain_rlp_of_isRobinImage_rlp hR hL td α hg⟩ = hg.1.toLp g
  exact robinOpVal_eq_rlp hR hL td α (MemLp.coeFn_toLp u.memL2).symm hg

/-! ## Symmetry and nonnegativity -/

/-- **Symmetry of the Robin operator.** -/
theorem robinOp_symm_rlp (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (td : TraceData Cm Cp L R)
    (α : ℝ) (x y : robinDomain_rlp hR hL td α) :
    ⟪robinOp_rlp hR hL td α x, (y : robinH_rlp Cm Cp L R)⟫ =
      ⟪(x : robinH_rlp Cm Cp L R), robinOp_rlp hR hL td α y⟫ := by
  have hux := robinRep_rlp_toFun_ae hR hL td α x
  have hwy := robinRep_rlp_toFun_ae hR hL td α y
  have hgx := robinImg_rlp_isRobinImage hR hL td α x
  have hgy := robinImg_rlp_isRobinImage hR hL td α y
  have hLHSval : robinOp_rlp hR hL td α x = hgx.1.toLp (robinImg_rlp hR hL td α x) := rfl
  have hRHSval : robinOp_rlp hR hL td α y = hgy.1.toLp (robinImg_rlp hR hL td α y) := rfl
  rw [hLHSval, hRHSval, inner_eq_integral_rlp, inner_eq_integral_rlp]
  have hLco : (hgx.1.toLp (robinImg_rlp hR hL td α x) : CapSpace m → ℝ)
      =ᵐ[volume.restrict (thinDomain Cm Cp L R)] robinImg_rlp hR hL td α x :=
    MemLp.coeFn_toLp hgx.1
  have hRco : (hgy.1.toLp (robinImg_rlp hR hL td α y) : CapSpace m → ℝ)
      =ᵐ[volume.restrict (thinDomain Cm Cp L R)] robinImg_rlp hR hL td α y :=
    MemLp.coeFn_toLp hgy.1
  have key := isRobinImage_symm_rop hgx hgy
  have step1 : (∫ p in thinDomain Cm Cp L R,
        (hgx.1.toLp (robinImg_rlp hR hL td α x) : CapSpace m → ℝ) p
          * (y : robinH_rlp Cm Cp L R) p)
      = ∫ p in thinDomain Cm Cp L R,
          robinImg_rlp hR hL td α x p * (robinRep_rlp hR hL td α y).toFun p := by
    refine integral_congr_ae ?_
    filter_upwards [hLco, hwy] with p hp1 hp2
    rw [hp1, ← hp2]
  have step2 : (∫ p in thinDomain Cm Cp L R,
        (x : robinH_rlp Cm Cp L R) p
          * (hgy.1.toLp (robinImg_rlp hR hL td α y) : CapSpace m → ℝ) p)
      = ∫ p in thinDomain Cm Cp L R,
          (robinRep_rlp hR hL td α x).toFun p * robinImg_rlp hR hL td α y p := by
    refine integral_congr_ae ?_
    filter_upwards [hux, hRco] with p hp1 hp2
    rw [← hp1, hp2]
  rw [step1, step2]
  exact key

/-- **Nonnegativity of the Robin operator**, for `α ≥ 0`. -/
theorem robinOp_nonneg_rlp (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (td : TraceData Cm Cp L R)
    {α : ℝ} (hα : 0 ≤ α) (x : robinDomain_rlp hR hL td α) :
    0 ≤ ⟪robinOp_rlp hR hL td α x, (x : robinH_rlp Cm Cp L R)⟫ := by
  have hux := robinRep_rlp_toFun_ae hR hL td α x
  have hgx := robinImg_rlp_isRobinImage hR hL td α x
  have hLHSval : robinOp_rlp hR hL td α x = hgx.1.toLp (robinImg_rlp hR hL td α x) := rfl
  rw [hLHSval, inner_eq_integral_rlp]
  have hLco : (hgx.1.toLp (robinImg_rlp hR hL td α x) : CapSpace m → ℝ)
      =ᵐ[volume.restrict (thinDomain Cm Cp L R)] robinImg_rlp hR hL td α x :=
    MemLp.coeFn_toLp hgx.1
  have key := isRobinImage_nonneg_rop hα hgx
  have step : (∫ p in thinDomain Cm Cp L R,
        (hgx.1.toLp (robinImg_rlp hR hL td α x) : CapSpace m → ℝ) p
          * (x : robinH_rlp Cm Cp L R) p)
      = ∫ p in thinDomain Cm Cp L R,
          robinImg_rlp hR hL td α x p * (robinRep_rlp hR hL td α x).toFun p := by
    refine integral_congr_ae ?_
    filter_upwards [hLco, hux] with p hp1 hp2
    rw [hp1, ← hp2]
  rw [step]
  exact key

/-! ## Solvability of `(-Δ+1)v = h` and surjectivity of `robinOp_rlp + 1` -/

/-- **Surjectivity of `robinOp_rlp + 1`**, from weak solvability of the Robin problem
`(-Δ+1)v = h` (`RobinLaxMilgramProp`). -/
theorem robinOp_add_one_surj_rlp (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (td : TraceData Cm Cp L R) (α : ℝ) (hLM : RobinLaxMilgramProp td α)
    (h : robinH_rlp Cm Cp L R) :
    ∃ x : robinDomain_rlp hR hL td α,
      robinOp_rlp hR hL td α x + (x : robinH_rlp Cm Cp L R) = h := by
  obtain ⟨v, hv⟩ := hLM (h : CapSpace m → ℝ) (Lp.memLp h)
  set f : CapSpace m → ℝ := fun p => (h : CapSpace m → ℝ) p - v.toFun p with hfdef
  have hfMemLp : MemLp f 2 (volume.restrict (thinDomain Cm Cp L R)) :=
    (Lp.memLp h).sub v.memL2
  have hIm : IsRobinImage_rop td α v f := by
    refine ⟨hfMemLp, fun φ => ?_⟩
    have heq := hv φ
    have hmb : massBilinP v φ = ∫ p in thinDomain Cm Cp L R, v.toFun p * φ.toFun p := rfl
    have hInt1 : Integrable (fun p => (h : CapSpace m → ℝ) p * φ.toFun p)
        (volume.restrict (thinDomain Cm Cp L R)) := (Lp.memLp h).integrable_mul φ.memL2
    have hInt2 : Integrable (fun p => v.toFun p * φ.toFun p)
        (volume.restrict (thinDomain Cm Cp L R)) := v.memL2.integrable_mul φ.memL2
    have hInt : (∫ p in thinDomain Cm Cp L R, f p * φ.toFun p)
        = (∫ p in thinDomain Cm Cp L R, (h : CapSpace m → ℝ) p * φ.toFun p)
          - ∫ p in thinDomain Cm Cp L R, v.toFun p * φ.toFun p := by
      rw [← integral_sub hInt1 hInt2]
      exact integral_congr_ae (.of_forall fun p => by simp only [hfdef]; ring)
    rw [hInt]
    linarith [heq, hmb]
  refine ⟨⟨v.memL2.toLp v.toFun, mem_robinDomain_rlp_of_isRobinImage_rlp hR hL td α hIm⟩, ?_⟩
  have hop : robinOp_rlp hR hL td α
      ⟨v.memL2.toLp v.toFun, mem_robinDomain_rlp_of_isRobinImage_rlp hR hL td α hIm⟩
      = hfMemLp.toLp f := robinOp_apply_rlp hR hL td α hIm
  rw [hop]
  have hfun : f + v.toFun = (h : CapSpace m → ℝ) := by
    funext p; simp only [hfdef, Pi.add_apply]; ring
  have hae : (f + v.toFun) =ᵐ[volume.restrict (thinDomain Cm Cp L R)] (h : CapSpace m → ℝ) := by
    rw [hfun]
  exact (MemLp.toLp_add hfMemLp v.memL2).symm.trans
    ((MemLp.toLp_congr (hfMemLp.add v.memL2) (Lp.memLp h) hae).trans
      (Lp.toLp_coeFn h (Lp.memLp h)))

/-! ## Self-adjointness -/

/-- **Self-adjointness of the Robin operator**, under the abstract criterion
`SelfAdjointCriterionProp` and weak solvability `RobinLaxMilgramProp`. -/
theorem robinOp_isSelfAdjoint_rlp (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (td : TraceData Cm Cp L R) {α : ℝ} (hα : 0 ≤ α) (hLM : RobinLaxMilgramProp td α)
    (hcrit : SelfAdjointCriterionProp) : IsSelfAdjoint (robinOp_rlp hR hL td α) :=
  hcrit (robinH_rlp Cm Cp L R) (robinOp_rlp hR hL td α) (robinOp_symm_rlp hR hL td α)
    (robinOp_nonneg_rlp hR hL td hα) (robinOp_add_one_surj_rlp hR hL td α hLM)

/-! ## The spectrum of the Robin operator -/

theorem massP_pos_of_ne_zero_rlp {u : H1P (thinDomain Cm Cp L R)} {x : robinH_rlp Cm Cp L R}
    (hux : u.toFun =ᵐ[volume.restrict (thinDomain Cm Cp L R)] (x : CapSpace m → ℝ))
    (hx : x ≠ 0) : 0 < massP u := by
  rcases (massP_nonneg u).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hx
    have hmem : u ∈ nullAEP (thinDomain Cm Cp L R) := mem_nullAEP_of_massP_eq_zero h.symm
    have hu0 : u.toFun =ᵐ[volume.restrict (thinDomain Cm Cp L R)] 0 := hmem
    have hx0 : (x : CapSpace m → ℝ) =ᵐ[volume.restrict (thinDomain Cm Cp L R)] 0 :=
      hux.symm.trans hu0
    have hz0 : ((0 : robinH_rlp Cm Cp L R) : CapSpace m → ℝ)
        =ᵐ[volume.restrict (thinDomain Cm Cp L R)] (0 : CapSpace m → ℝ) :=
      Lp.coeFn_zero ℝ 2 (volume.restrict (thinDomain Cm Cp L R))
    exact Lp.ext (hx0.trans hz0.symm)

/-- **The eigenvalues of the Robin operator are exactly the variational values
`lambdaThin hR hL td α (a+1)`.** -/
theorem robinOp_eigen_iff_rlp (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (td : TraceData Cm Cp L R)
    {α : ℝ} (hα : 0 ≤ α) (μ : ℝ) :
    (∃ x : robinDomain_rlp hR hL td α, (x : robinH_rlp Cm Cp L R) ≠ 0 ∧
        robinOp_rlp hR hL td α x = μ • (x : robinH_rlp Cm Cp L R)) ↔
      ∃ a : ℕ, μ = lambdaThin hR hL td α (a + 1) := by
  rw [← robinOperator_spectrum_final hR hL td hα μ]
  constructor
  · rintro ⟨x, hxne, hxeq⟩
    have hux := robinRep_rlp_toFun_ae hR hL td α x
    have hgx := robinImg_rlp_isRobinImage hR hL td α x
    have hLHSval : robinOp_rlp hR hL td α x = hgx.1.toLp (robinImg_rlp hR hL td α x) := rfl
    have hHeq : hgx.1.toLp (robinImg_rlp hR hL td α x) = μ • (x : robinH_rlp Cm Cp L R) := by
      rw [← hLHSval]; exact hxeq
    have e1 : robinImg_rlp hR hL td α x =ᵐ[volume.restrict (thinDomain Cm Cp L R)]
        (hgx.1.toLp (robinImg_rlp hR hL td α x) : CapSpace m → ℝ) :=
      (MemLp.coeFn_toLp hgx.1).symm
    rw [hHeq] at e1
    have hgxeq : robinImg_rlp hR hL td α x =ᵐ[volume.restrict (thinDomain Cm Cp L R)]
        μ • (robinRep_rlp hR hL td α x).toFun := by
      refine e1.trans ((Lp.coeFn_smul μ (x : robinH_rlp Cm Cp L R)).trans ?_)
      exact hux.symm.fun_comp (μ • ·)
    have himg2 : IsRobinImage_rop td α (robinRep_rlp hR hL td α x)
        (μ • (robinRep_rlp hR hL td α x).toFun) :=
      isRobinImage_ae_congr_image_rlp hgxeq hgx
    exact ⟨robinRep_rlp hR hL td α x, massP_pos_of_ne_zero_rlp hux hxne, himg2⟩
  · rintro ⟨u, hu_pos, himg⟩
    refine ⟨⟨u.memL2.toLp u.toFun, mem_robinDomain_rlp_of_isRobinImage_rlp hR hL td α himg⟩,
      ?_, ?_⟩
    · intro hzero
      have hzero' : u.memL2.toLp u.toFun = (0 : robinH_rlp Cm Cp L R) := hzero
      have h1 : (u.memL2.toLp u.toFun : CapSpace m → ℝ)
          =ᵐ[volume.restrict (thinDomain Cm Cp L R)] u.toFun := MemLp.coeFn_toLp u.memL2
      rw [hzero'] at h1
      have h2 : ((0 : robinH_rlp Cm Cp L R) : CapSpace m → ℝ)
          =ᵐ[volume.restrict (thinDomain Cm Cp L R)] (0 : CapSpace m → ℝ) :=
        Lp.coeFn_zero ℝ 2 (volume.restrict (thinDomain Cm Cp L R))
      have hu0 : u.toFun =ᵐ[volume.restrict (thinDomain Cm Cp L R)] 0 := h1.symm.trans h2
      have hmz : massP u = 0 := by
        unfold massP
        have hz2 : (fun p => u.toFun p ^ 2)
            =ᵐ[volume.restrict (thinDomain Cm Cp L R)] fun _ => (0 : ℝ) := by
          filter_upwards [hu0] with p hp
          simp only [Pi.zero_apply] at hp
          simp [hp]
        rw [integral_congr_ae hz2, integral_zero]
      linarith
    · have hop : robinOp_rlp hR hL td α
          ⟨u.memL2.toLp u.toFun, mem_robinDomain_rlp_of_isRobinImage_rlp hR hL td α himg⟩
          = himg.1.toLp (μ • u.toFun) := robinOp_apply_rlp hR hL td α himg
      rw [hop]
      exact MemLp.toLp_const_smul μ u.memL2

end RobinCaps.ThinDomain

end
