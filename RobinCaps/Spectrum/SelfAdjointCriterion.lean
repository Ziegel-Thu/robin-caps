import RobinCaps.ThinDomain.SelfAdjointIface
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# A self-adjointness criterion for symmetric, nonnegative, surjective `LinearPMap`s

This file discharges the abstract hypothesis `RobinCaps.ThinDomain.SelfAdjointCriterionProp`
from `RobinCaps.ThinDomain.SelfAdjointIface`: in a real Hilbert space `H`, a partially defined
linear operator `A : H →ₗ.[ℝ] H` (mathlib's `LinearPMap`) which is

* symmetric on its domain (`hsym`): `⟪A x, y⟫ = ⟪x, A y⟫` for `x y` in `A.domain`,
* nonnegative on its domain (`hpos`): `0 ≤ ⟪A x, x⟫` for `x` in `A.domain`, and
* such that `A + 1` is surjective onto `H` (`hsurj`): every `h : H` is `A x + x` for some
  `x` in `A.domain`,

is self-adjoint, i.e. `A.adjoint = A` (mathlib's `LinearPMap.adjoint`, notation `A†`, from
`Mathlib/Analysis/InnerProductSpace/LinearPMap.lean`).

## Proof outline

* `A + 1` is injective on `A.domain` (`hInj`): if `A x + x = 0` then
  `0 = ⟪A x + x, x⟫ = ⟪A x, x⟫ + ‖x‖ ^ 2 ≥ ‖x‖ ^ 2`, so `x = 0`.
* Together with `hsurj`, every `h : H` has a *unique* preimage under `x ↦ A x + x`; write
  `T h` for this preimage (an element of `A.domain`), produced via `Exists.choose`.
* `T` is symmetric as a map `H → H` (`hTsym`): `⟪T h, k⟫ = ⟪h, T k⟫` for all `h k : H`,
  using `hsym`.
* Consequently the orthogonal complement of `A.domain` is trivial (`hOrthoBot`): if
  `u ⊥ A.domain` then `⟪T h, u⟫ = 0` for every `h`, so `⟪h, T u⟫ = 0` for every `h`
  (by `hTsym`), so `T u = 0`, so `u = A (T u) + T u = 0`. Hence `A.domain` is dense
  (`hDense`), which is exactly what `LinearPMap.adjoint` needs to be well-behaved.
* `A ≤ A.adjoint` (`hAle`) follows from `hsym` via `LinearPMap.IsFormalAdjoint.le_adjoint`.
* `A.adjoint ≤ A` (`hAge`): given `x` in the domain of `A.adjoint`, solving
  `A x0 + x0 = A.adjoint x + x` via `hsurj` and comparing against every `w : A.domain`
  (using `hsym` and the defining property of `A.adjoint`, `LinearPMap.adjoint_isFormalAdjoint`)
  forces `x0 = x` (as elements of `H`) and `A x0 = A.adjoint x` (`key`). Hence
  `A.adjoint.domain ≤ A.domain` and the two maps agree there.
* `A.adjoint = A` by antisymmetry of `≤` on `LinearPMap`s, i.e. `IsSelfAdjoint A`
  (`LinearPMap.isSelfAdjoint_def`).
-/

noncomputable section

open scoped InnerProductSpace RealInnerProductSpace

namespace RobinCaps.Spectrum

/-- The self-adjointness criterion, for a fixed real Hilbert space `H` and a fixed
`A : H →ₗ.[ℝ] H`. This is the content of `RobinCaps.ThinDomain.SelfAdjointCriterionProp`,
specialized. -/
theorem selfAdjoint_of_sym_pos_surj_sac {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (A : H →ₗ.[ℝ] H)
    (hsym : ∀ x y : A.domain, ⟪A x, (y : H)⟫ = ⟪(x : H), A y⟫)
    (hpos : ∀ x : A.domain, 0 ≤ ⟪A x, (x : H)⟫)
    (hsurj : ∀ h : H, ∃ x : A.domain, A x + (x : H) = h) :
    IsSelfAdjoint A := by
  -- Step 1: `A + 1` is injective on `A.domain`.
  have hInj : ∀ x : A.domain, A x + (x : H) = 0 → x = 0 := by
    intro x hx
    have h1 : ⟪A x, (x : H)⟫ + ⟪(x : H), (x : H)⟫ = 0 := by
      rw [← inner_add_left, hx, inner_zero_left]
    have h3 := hpos x
    have h4 : ⟪(x : H), (x : H)⟫ ≤ 0 := by linarith
    have h5 : (0 : ℝ) ≤ ⟪(x : H), (x : H)⟫ := by
      rw [real_inner_self_eq_norm_sq]; positivity
    have h6 : ⟪(x : H), (x : H)⟫ = 0 := le_antisymm h4 h5
    have h7 : (x : H) = 0 := inner_self_eq_zero.mp h6
    exact Submodule.coe_eq_zero.mp h7
  -- The (choice-based) inverse `T` of `x ↦ A x + x`, and its defining equation.
  let T : H → A.domain := fun h => (hsurj h).choose
  have hT : ∀ h : H, A (T h) + ((T h : A.domain) : H) = h := fun h => (hsurj h).choose_spec
  -- Step 1 continued: `T` is a symmetric map `H → H`.
  have hTsym : ∀ h k : H, ⟪(T h : H), k⟫ = ⟪h, (T k : H)⟫ := by
    intro h k
    have e1 : A (T h) + (T h : H) = h := hT h
    have e2 : A (T k) + (T k : H) = k := hT k
    calc ⟪(T h : H), k⟫
        = ⟪(T h : H), A (T k) + (T k : H)⟫ :=
          congrArg (fun v : H => (⟪(T h : H), v⟫ : ℝ)) e2.symm
      _ = ⟪(T h : H), A (T k)⟫ + ⟪(T h : H), (T k : H)⟫ := inner_add_right _ _ _
      _ = ⟪A (T h), (T k : H)⟫ + ⟪(T h : H), (T k : H)⟫ := by rw [← hsym (T h) (T k)]
      _ = ⟪A (T h) + (T h : H), (T k : H)⟫ := (inner_add_left _ _ _).symm
      _ = ⟪h, (T k : H)⟫ := by rw [e1]
  -- Step 2: the orthogonal complement of `A.domain` is trivial, hence `A.domain` is dense.
  have hOrthoBot : (A.domain)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro u0 hu0
    have hu0' : ∀ h : H, ⟪(T h : H), u0⟫ = 0 := fun h =>
      Submodule.inner_right_of_mem_orthogonal (T h).2 hu0
    have hu1 : ∀ h : H, ⟪h, (T u0 : H)⟫ = 0 := fun h => (hTsym h u0).symm.trans (hu0' h)
    have hu2 : ⟪(T u0 : H), (T u0 : H)⟫ = 0 := hu1 (T u0 : H)
    have hu3 : (T u0 : H) = 0 := inner_self_eq_zero.mp hu2
    have hu4 : T u0 = 0 := Submodule.coe_eq_zero.mp hu3
    have hu5 := hT u0
    rw [hu4] at hu5
    simpa using hu5.symm
  have hDense : Dense (A.domain : Set H) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr
      (Submodule.topologicalClosure_eq_top_iff.mpr hOrthoBot)
  -- Step 3: `A ≤ A.adjoint`, since `A` is a formal adjoint of itself.
  have hFA : A.IsFormalAdjoint A := hsym
  have hAle : A ≤ A.adjoint := hFA.le_adjoint hDense
  -- Step 4: `A.adjoint ≤ A`.
  have hFAadj : A.adjoint.IsFormalAdjoint A := LinearPMap.adjoint_isFormalAdjoint (T := A) hDense
  have key : ∀ x : A.adjoint.domain, ∃ x0 : A.domain,
      (x0 : H) = (x : H) ∧ A x0 = A.adjoint x := by
    intro x
    have hform : ∀ w : A.domain, ⟪A.adjoint x, (w : H)⟫ = ⟪(x : H), A w⟫ := fun w => hFAadj x w
    obtain ⟨x0, hx0⟩ := hsurj (A.adjoint x + (x : H))
    have step3 : A x0 = A.adjoint x + (x : H) - (x0 : H) := eq_sub_iff_add_eq.mpr hx0
    have main : ∀ w : A.domain, ⟪A w + (w : H), (x : H)⟫ = ⟪A w + (w : H), (x0 : H)⟫ := by
      intro w
      have step1 : ⟪A w, (x : H)⟫ = ⟪(w : H), A.adjoint x⟫ := by
        calc ⟪A w, (x : H)⟫ = ⟪(x : H), A w⟫ := (real_inner_comm (A w) (x : H)).symm
          _ = ⟪A.adjoint x, (w : H)⟫ := (hform w).symm
          _ = ⟪(w : H), A.adjoint x⟫ := (real_inner_comm (A.adjoint x) (w : H)).symm
      have step2 : ⟪A w, (x0 : H)⟫ = ⟪(w : H), A x0⟫ := hsym w x0
      have hL : ⟪A w + (w : H), (x : H)⟫ = ⟪(w : H), A.adjoint x⟫ + ⟪(w : H), (x : H)⟫ := by
        rw [inner_add_left, step1]
      have hR : ⟪A w + (w : H), (x0 : H)⟫ = ⟪(w : H), A.adjoint x⟫ + ⟪(w : H), (x : H)⟫ := by
        rw [inner_add_left, step2, step3, inner_sub_right, inner_add_right]
        ring
      exact hL.trans hR.symm
    have hall : ∀ h : H, ⟪h, (x : H)⟫ = ⟪h, (x0 : H)⟫ := by
      intro h
      obtain ⟨w, hw⟩ := hsurj h
      have hmw := main w
      rwa [hw] at hmw
    have h1 : ⟪(x : H) - (x0 : H), (x : H) - (x0 : H)⟫ = 0 := by
      rw [inner_sub_right]
      linarith [hall ((x : H) - (x0 : H))]
    have hEqVec : (x : H) = (x0 : H) := sub_eq_zero.mp (inner_self_eq_zero.mp h1)
    refine ⟨x0, hEqVec.symm, ?_⟩
    rw [step3, hEqVec]
    abel
  have hDomLe : A.adjoint.domain ≤ A.domain := by
    intro z hz
    obtain ⟨x0, hx0eq, _⟩ := key ⟨z, hz⟩
    have hz' : (x0 : H) = z := hx0eq
    exact hz' ▸ x0.2
  have hPointwiseEq : ∀ ⦃x : A.adjoint.domain⦄ ⦃y : A.domain⦄ (_h : (x : H) = (y : H)),
      A.adjoint x = A y := by
    intro x y hxy
    obtain ⟨x0, hx0eq, hAx0⟩ := key x
    have hx0y : x0 = y := Subtype.ext (hx0eq.trans hxy)
    rw [← hAx0, hx0y]
  have hAge : A.adjoint ≤ A := ⟨hDomLe, hPointwiseEq⟩
  -- Conclusion: `A.adjoint = A`, i.e. `A` is self-adjoint.
  exact LinearPMap.isSelfAdjoint_def.mpr (le_antisymm hAge hAle)

/-- The abstract self-adjointness criterion `RobinCaps.ThinDomain.SelfAdjointCriterionProp`. -/
theorem selfAdjointCriterion_sac : RobinCaps.ThinDomain.SelfAdjointCriterionProp :=
  fun _H _ _ _ A hsym hpos hsurj => selfAdjoint_of_sym_pos_surj_sac A hsym hpos hsurj

end RobinCaps.Spectrum
