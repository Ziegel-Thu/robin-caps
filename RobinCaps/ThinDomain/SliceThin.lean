import RobinCaps.ThinDomain.Slice
import RobinCaps.Domain.ThinConvex

/-!
# Slice-wise (ACL) properties on the thin domain `Ω_R`

This file extends the slice results of `RobinCaps/ThinDomain/Slice.lean` from a product
cylinder `(a,b) ×ˢ B` to the **thin domain**

`Ω_R = {(x,z) | -L/2 < x < L/2, ‖z‖ < r_R x}`,

an "axially varying product": every transverse slice is an open ball whose radius is the
concave profile `r_R = RobinCaps.Domain.profile Cm Cp L R`.

## Strategy

The thin domain is exhausted by genuine product cylinders

`Ioo (levelInf t) (levelSup t) ×ˢ ball 0 t ⊆ Ω_R`,

where `levelSet t = {x ∈ (-L/2, L/2) | t < r_R x}` is the axial level set — an *interval*
`Ioo (levelInf t) (levelSup t)` because `r_R` is concave (`Domain.concaveOn_profile`) and
continuous (`Domain.continuousOn_profile`).  On each such cylinder the cylinder results of
`Slice.lean` apply verbatim to the restriction of `u` (`H1P.restrictTo`), and the exceptional
null set is removed by letting the radius run through the **rationals**: countably many null
sets, one union.  A test function on a slice has compact support, hence sits inside a cylinder
of rational radius, which is exactly what makes the countable exhaustion sufficient
(`hasWeakGrad_ball_of_rat`, `hasWeakDeriv_of_rat_subinterval`).

## Contents

* `levelSet`, `levelInf`, `levelSup`, `aZ`, `bZ`; `levelSet_eq_Ioo`, `mem_levelSet_of_between`.
* `thinDomain_transverseSlice`, `thinDomain_axialSlice` (**deliverable 1**).
* `sliceACL_transverse_thin`, `sliceACL_thin` (**deliverable 2**).
* `sliceACL_axial_thin`, `sliceACLAxial_thin` (**deliverable 3**).

Everything is proved without `sorry`, `axiom`, `admit` or `native_decide`.
-/

open MeasureTheory Set Filter Metric

open scoped ContDiff ENNReal Topology

namespace RobinCaps.ThinDomain

open RobinCaps.Domain

noncomputable section

variable {m : ℕ}

/-! ### Generic measure-theoretic and integral helpers -/

/-- An a.e. statement on `μ.restrict S` becomes an a.e. *implication* on any other restriction. -/
theorem ae_imp_of_ae_restrict {α : Type*} [MeasurableSpace α] {μ : Measure α} {S : Set α}
    (hS : MeasurableSet S) (T : Set α) {P : α → Prop} (h : ∀ᵐ x ∂(μ.restrict S), P x) :
    ∀ᵐ x ∂(μ.restrict T), x ∈ S → P x :=
  ae_restrict_of_ae ((ae_restrict_iff' hS).1 h)

/-- A test function supported in `S` only sees `S` (right-hand pairing, on `ℝ`). -/
theorem setIntegral_mul_test_eq_integral {S : Set ℝ} {f φ : ℝ → ℝ} (hS : tsupport φ ⊆ S) :
    (∫ x in S, f x * φ x) = ∫ x, f x * φ x := by
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
  rw [image_eq_zero_of_notMem_tsupport fun h => hx (hS h), mul_zero]

/-- A test function supported in `S` only sees `S` (left-hand pairing with `deriv φ`, on `ℝ`). -/
theorem setIntegral_mul_deriv_eq_integral {S : Set ℝ} {f φ : ℝ → ℝ} (hS : tsupport φ ⊆ S) :
    (∫ x in S, f x * deriv φ x) = ∫ x, f x * deriv φ x := by
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
  have hxs : x ∉ tsupport φ := fun h => hx (hS h)
  have hd : deriv φ x = 0 :=
    Function.notMem_support.1 fun h => hxs (support_deriv_subset h)
  rw [hd, mul_zero]

/-- An open, order-connected, bounded subset of `ℝ` is the open interval between its bounds
(the empty set included, since `sInf ∅ = sSup ∅ = 0`). -/
theorem eq_Ioo_of_isOpen_ordConnected {S : Set ℝ} (hopen : IsOpen S) (hconn : S.OrdConnected)
    (hbddA : BddAbove S) (hbddB : BddBelow S) : S = Ioo (sInf S) (sSup S) := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · rw [Real.sInf_empty, Real.sSup_empty, Ioo_self]
  · ext x
    constructor
    · intro hx
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen x hx
      have h1 : x - ε / 2 ∈ S := by
        refine hball ?_
        rw [Metric.mem_ball, Real.dist_eq, show x - ε / 2 - x = -(ε / 2) from by ring, abs_neg,
          abs_of_pos (by linarith)]
        linarith
      have h2 : x + ε / 2 ∈ S := by
        refine hball ?_
        rw [Metric.mem_ball, Real.dist_eq, show x + ε / 2 - x = ε / 2 from by ring,
          abs_of_pos (by linarith)]
        linarith
      refine ⟨?_, ?_⟩
      · have := csInf_le hbddB h1; linarith
      · have := le_csSup hbddA h2; linarith
    · rintro ⟨h1, h2⟩
      obtain ⟨p, hp, hpx⟩ := exists_lt_of_csInf_lt hne h1
      obtain ⟨q, hq, hxq⟩ := exists_lt_of_lt_csSup hne h2
      exact hconn.out hp hq ⟨hpx.le, hxq.le⟩

/-! ### Restriction of an `H1P` element to a subset -/

/-- **Restriction of an element of `H1P Ω` to a subset `Ω' ⊆ Ω`.**  The three representatives
are unchanged; square integrability restricts and the weak-gradient identity is
`HasWeakGradP.mono`. -/
def H1P.restrictTo {Ω Ω' : Set (CapSpace m)} (u : H1P Ω) (hsub : Ω' ⊆ Ω) : H1P Ω' where
  toFun := u.toFun
  gx := u.gx
  gz := u.gz
  memL2 := by
    have h : (volume.restrict Ω).restrict Ω' = (volume : Measure (CapSpace m)).restrict Ω' :=
      Measure.restrict_restrict_of_subset hsub
    rw [← h]; exact u.memL2.restrict Ω'
  gx_memL2 := by
    have h : (volume.restrict Ω).restrict Ω' = (volume : Measure (CapSpace m)).restrict Ω' :=
      Measure.restrict_restrict_of_subset hsub
    rw [← h]; exact u.gx_memL2.restrict Ω'
  gz_memL2 := by
    have h : (volume.restrict Ω).restrict Ω' = (volume : Measure (CapSpace m)).restrict Ω' :=
      Measure.restrict_restrict_of_subset hsub
    rw [← h]; exact u.gz_memL2.restrict Ω'
  hasWeakGrad := HasWeakGradP.mono hsub u.hasWeakGrad

@[simp] theorem H1P.restrictTo_toFun {Ω Ω' : Set (CapSpace m)} (u : H1P Ω) (hsub : Ω' ⊆ Ω) :
    (u.restrictTo hsub).toFun = u.toFun := rfl

@[simp] theorem H1P.restrictTo_gx {Ω Ω' : Set (CapSpace m)} (u : H1P Ω) (hsub : Ω' ⊆ Ω) :
    (u.restrictTo hsub).gx = u.gx := rfl

@[simp] theorem H1P.restrictTo_gz {Ω Ω' : Set (CapSpace m)} (u : H1P Ω) (hsub : Ω' ⊆ Ω) :
    (u.restrictTo hsub).gz = u.gz := rfl

/-! ### The axial level sets of the profile -/

variable (Cm Cp : Cap m) (L R : ℝ)

/-- The **axial level set** `{x ∈ (-L/2, L/2) | t < r_R x}`: the set of axial coordinates at
which the transverse slice of `Ω_R` contains the sphere of radius `t`. -/
def levelSet (t : ℝ) : Set ℝ := {x ∈ Ioo (-L / 2) (L / 2) | t < profile Cm Cp L R x}

/-- The left endpoint of the axial level set. -/
def levelInf (t : ℝ) : ℝ := sInf (levelSet Cm Cp L R t)

/-- The right endpoint of the axial level set. -/
def levelSup (t : ℝ) : ℝ := sSup (levelSet Cm Cp L R t)

/-- The left endpoint of the axial slice of `Ω_R` through the transverse point `z`. -/
def aZ (z : EuclideanSpace ℝ (Fin m)) : ℝ := levelInf Cm Cp L R ‖z‖

/-- The right endpoint of the axial slice of `Ω_R` through the transverse point `z`. -/
def bZ (z : EuclideanSpace ℝ (Fin m)) : ℝ := levelSup Cm Cp L R ‖z‖

variable {Cm Cp L R}

theorem mem_levelSet_iff {t x : ℝ} :
    x ∈ levelSet Cm Cp L R t ↔ x ∈ Ioo (-L / 2) (L / 2) ∧ t < profile Cm Cp L R x := Iff.rfl

theorem levelSet_subset (t : ℝ) : levelSet Cm Cp L R t ⊆ Ioo (-L / 2) (L / 2) := fun _ hx => hx.1

/-- The level sets are open: the profile is continuous on the (open) axial interval. -/
theorem isOpen_levelSet (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (t : ℝ) :
    IsOpen (levelSet Cm Cp L R t) := by
  have h := (continuousOn_profile (Cm := Cm) (Cp := Cp) hR hL).isOpen_inter_preimage
    isOpen_Ioo (isOpen_Ioi (a := t))
  exact h

theorem measurableSet_levelSet (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (t : ℝ) :
    MeasurableSet (levelSet Cm Cp L R t) := (isOpen_levelSet hR hL t).measurableSet

/-- The level sets are convex: the profile is concave. -/
theorem convex_levelSet (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (t : ℝ) :
    Convex ℝ (levelSet Cm Cp L R t) :=
  (concaveOn_profile (Cm := Cm) (Cp := Cp) hR hL).convex_gt t

/-- **The axial level set is an open interval.** -/
theorem levelSet_eq_Ioo (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (t : ℝ) :
    levelSet Cm Cp L R t = Ioo (levelInf Cm Cp L R t) (levelSup Cm Cp L R t) := by
  refine eq_Ioo_of_isOpen_ordConnected (isOpen_levelSet hR hL t)
    ((convex_levelSet hR hL t).ordConnected) ?_ ?_
  · exact ⟨L / 2, fun x hx => (levelSet_subset t hx).2.le⟩
  · exact ⟨-L / 2, fun x hx => (levelSet_subset t hx).1.le⟩

/-- **Membership from betweenness** (the "interval" form of the level set). -/
theorem mem_levelSet_of_between (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) {t x : ℝ}
    (h1 : levelInf Cm Cp L R t < x) (h2 : x < levelSup Cm Cp L R t) :
    x ∈ levelSet Cm Cp L R t := by
  rw [levelSet_eq_Ioo hR hL]; exact ⟨h1, h2⟩

/-- Above the maximal radius the level set is empty. -/
theorem levelSet_eq_empty (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) {t : ℝ} (ht : R ≤ t) :
    levelSet Cm Cp L R t = (∅ : Set ℝ) := by
  ext x
  simp only [mem_empty_iff_false, iff_false, mem_levelSet_iff, not_and, not_lt]
  exact fun hx => (profile_le_R hR hL hx).trans ht

/-! ### Deliverable 1: the two slice descriptions -/

/-- **The transverse slice of the thin domain** is the ball of radius `r_R x` for `x` in the
axial interval, and empty outside. -/
theorem thinDomain_transverseSlice (x : ℝ) :
    {z : EuclideanSpace ℝ (Fin m) | (x, z) ∈ thinDomain Cm Cp L R}
      = if x ∈ Ioo (-L / 2) (L / 2) then ball (0 : EuclideanSpace ℝ (Fin m))
          (profile Cm Cp L R x) else (∅ : Set (EuclideanSpace ℝ (Fin m))) := by
  by_cases hx : x ∈ Ioo (-L / 2) (L / 2)
  · rw [if_pos hx]
    ext z
    simp [thinDomain, hx.1, hx.2]
  · rw [if_neg hx]
    ext z
    simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
    rw [mem_Ioo, not_and_or, not_lt, not_lt] at hx
    rintro ⟨h1, h2, -⟩
    rcases hx with h | h <;> linarith

/-- The axial slice of the thin domain is the level set of the profile at radius `‖z‖`. -/
theorem thinDomain_axialSlice_eq_levelSet (z : EuclideanSpace ℝ (Fin m)) :
    {x : ℝ | (x, z) ∈ thinDomain Cm Cp L R} = levelSet Cm Cp L R ‖z‖ := by
  ext x
  simp [thinDomain, levelSet, mem_Ioo, and_assoc]

/-- **The axial slice of the thin domain is an open interval** `(aZ z, bZ z)` — this is where
the concavity of the profile is used. -/
theorem thinDomain_axialSlice (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (z : EuclideanSpace ℝ (Fin m)) :
    {x : ℝ | (x, z) ∈ thinDomain Cm Cp L R} = Ioo (aZ Cm Cp L R z) (bZ Cm Cp L R z) := by
  rw [thinDomain_axialSlice_eq_levelSet, levelSet_eq_Ioo hR hL]
  rfl

/-- Outside the ball of radius `R` the axial slice is empty. -/
theorem thinDomain_axialSlice_eq_empty (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    {z : EuclideanSpace ℝ (Fin m)} (hz : R ≤ ‖z‖) :
    {x : ℝ | (x, z) ∈ thinDomain Cm Cp L R} = (∅ : Set ℝ) := by
  rw [thinDomain_axialSlice_eq_levelSet, levelSet_eq_empty hR hL hz]

/-! ### The exhausting cylinders -/

/-- **The exhausting product cylinders.**  For every radius `t`, the cylinder over the axial
level set at height `t` with transverse ball of radius `t` sits inside the thin domain. -/
theorem cylinder_subset_thinDomain (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (t : ℝ) :
    Ioo (levelInf Cm Cp L R t) (levelSup Cm Cp L R t)
        ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) t ⊆ thinDomain Cm Cp L R := by
  rintro ⟨x, z⟩ ⟨hx, hz⟩
  have hx' : x ∈ levelSet Cm Cp L R t := mem_levelSet_of_between hR hL hx.1 hx.2
  exact ⟨hx'.1.1, hx'.1.2, lt_trans (mem_ball_zero_iff.1 hz) hx'.2⟩

/-! ### Deliverable 2: the transverse ACL property on the thin domain -/

/-- **Exhaustion of a ball by rational sub-balls.**  If `g` is a weak gradient of `v` on every
ball of rational radius `q < ρ`, it is a weak gradient on `ball 0 ρ`: a test function supported
in `ball 0 ρ` has compact support, hence is supported in `ball 0 q` for some rational
`q < ρ`, and both sides of the identity are unchanged when the domain of integration is
shrunk to `ball 0 q`. -/
theorem hasWeakGrad_ball_of_rat {ρ : ℝ} {v : EuclideanSpace ℝ (Fin m) → ℝ}
    {g : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    (h : ∀ q : ℚ, (0 : ℝ) < (q : ℝ) → (q : ℝ) < ρ →
      RobinCaps.Sobolev.Weak.HasWeakGrad (ball (0 : EuclideanSpace ℝ (Fin m)) (q : ℝ)) v g) :
    RobinCaps.Sobolev.Weak.HasWeakGrad (ball (0 : EuclideanSpace ℝ (Fin m)) ρ) v g := by
  intro χ hχ hχc hχs i
  rcases eq_empty_or_nonempty (tsupport χ) with hemp | hne
  · have h0 : χ = fun _ => (0 : ℝ) := by
      funext z
      exact image_eq_zero_of_notMem_tsupport (by rw [hemp]; exact notMem_empty z)
    subst h0
    simp
  · obtain ⟨z₀, hz₀, hmax'⟩ := IsCompact.exists_isMaxOn (f := fun z => ‖z‖) hχc hne
      continuous_norm.continuousOn
    have hmax : ∀ z ∈ tsupport χ, ‖z‖ ≤ ‖z₀‖ := fun z hz => isMaxOn_iff.1 hmax' z hz
    have hz₀ρ : ‖z₀‖ < ρ := mem_ball_zero_iff.1 (hχs hz₀)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hz₀ρ
    have hqpos : (0 : ℝ) < (q : ℝ) := lt_of_le_of_lt (norm_nonneg z₀) hq1
    have hsubq : tsupport χ ⊆ ball (0 : EuclideanSpace ℝ (Fin m)) (q : ℝ) := fun z hz =>
      mem_ball_zero_iff.2 (lt_of_le_of_lt (hmax z hz) hq1)
    rw [RobinCaps.Sobolev.Weak.HasWeakGrad.setIntegral_mul_pderiv_eq_integral (u := v) i hχs,
      RobinCaps.Sobolev.Weak.HasWeakGrad.setIntegral_comp_mul_eq_integral (g := g) i hχs,
      ← RobinCaps.Sobolev.Weak.HasWeakGrad.setIntegral_mul_pderiv_eq_integral (u := v) i hsubq,
      ← RobinCaps.Sobolev.Weak.HasWeakGrad.setIntegral_comp_mul_eq_integral (g := g) i hsubq]
    exact h q hqpos hq2 χ hχ hχc hsubq i

/-- The cylinder result of `Slice.lean`, transported to the thin domain: for almost every `x`
in the axial level set at radius `t`, the transverse slice has the slice of `∇_z u` as a weak
gradient on the ball of radius `t`. -/
theorem sliceACL_transverse_level (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) (t : ℝ) :
    ∀ᵐ x ∂(volume.restrict (levelSet Cm Cp L R t)),
      RobinCaps.Sobolev.Weak.HasWeakGrad (ball (0 : EuclideanSpace ℝ (Fin m)) t)
        (fun z => u.toFun (x, z)) (fun z => u.gz (x, z)) := by
  have hsub := cylinder_subset_thinDomain hR hL t
  have h := sliceACL_transverse (u.restrictTo hsub)
  rw [levelSet_eq_Ioo hR hL]
  exact h

/-- **Deliverable 2 (transverse ACL on the thin domain).**  For almost every axial coordinate
`x ∈ (-L/2, L/2)`, the transverse slice `z ↦ u(x,z)` has `z ↦ (∇_z u)(x,z)` as a weak gradient
on the ball `B(0, r_R x)`, which is exactly the transverse slice of `Ω_R` at `x`. -/
theorem sliceACL_transverse_thin (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    ∀ᵐ x ∂(volume.restrict (Ioo (-L / 2) (L / 2))),
      RobinCaps.Sobolev.Weak.HasWeakGrad
        (ball (0 : EuclideanSpace ℝ (Fin m)) (profile Cm Cp L R x))
        (fun z => u.toFun (x, z)) (fun z => u.gz (x, z)) := by
  have key : ∀ q : ℚ, ∀ᵐ x ∂(volume.restrict (Ioo (-L / 2) (L / 2))),
      x ∈ levelSet Cm Cp L R (q : ℝ) →
        RobinCaps.Sobolev.Weak.HasWeakGrad (ball (0 : EuclideanSpace ℝ (Fin m)) (q : ℝ))
          (fun z => u.toFun (x, z)) (fun z => u.gz (x, z)) := fun q =>
    ae_imp_of_ae_restrict (measurableSet_levelSet hR hL _) _
      (sliceACL_transverse_level hR hL u (q : ℝ))
  filter_upwards [ae_all_iff.2 key, ae_restrict_mem measurableSet_Ioo] with x hx hxI
  exact hasWeakGrad_ball_of_rat fun q _ hqr => hx q ⟨hxI, hqr⟩

/-- **The `SliceACL` target of `RobinCaps/ThinDomain/H1P.lean` for the thin domain.** -/
theorem sliceACL_thin (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) : SliceACL (thinDomain Cm Cp L R) u := by
  have h := sliceACL_transverse_thin hR hL u
  rw [ae_restrict_iff' measurableSet_Ioo] at h
  filter_upwards [h] with x hx
  by_cases hxI : x ∈ Ioo (-L / 2) (L / 2)
  · rw [thinDomain_transverseSlice, if_pos hxI]
    exact hx hxI
  · rw [thinDomain_transverseSlice, if_neg hxI]
    intro φ hφ hφc hφs i
    simp

/-! ### Deliverable 3: the axial ACL property on the thin domain -/

/-- A closed axial interval on which the profile stays above `q` carries a product cylinder
inside the thin domain. -/
theorem cylinder_sub_subset_thinDomain {s t q : ℝ}
    (hIcc : Icc s t ⊆ levelSet Cm Cp L R q) :
    Ioo s t ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) q ⊆ thinDomain Cm Cp L R := by
  rintro ⟨x, z⟩ ⟨hx, hz⟩
  have hx' : x ∈ levelSet Cm Cp L R q := hIcc (Ioo_subset_Icc_self hx)
  exact ⟨hx'.1.1, hx'.1.2, lt_trans (mem_ball_zero_iff.1 hz) hx'.2⟩

/-- The cylinder result of `Slice.lean`, transported to the thin domain: on a closed axial
interval where the profile exceeds `q`, almost every axial line through `ball 0 q` has the
expected weak derivative. -/
theorem sliceACL_axial_sub (u : H1P (thinDomain Cm Cp L R)) {s t q : ℝ} (hst : s < t)
    (hIcc : Icc s t ⊆ levelSet Cm Cp L R q) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) q)),
      RobinCaps.Sobolev.HasWeakDeriv s t (fun x => u.toFun (x, z)) (fun x => u.gx (x, z)) :=
  sliceACL_axial hst isOpen_ball (u.restrictTo (cylinder_sub_subset_thinDomain hIcc))

/-- **Exhaustion of an axial slice by rational subintervals.**  If `g` is a weak derivative of
`v` on every rational interval `[s,t]` on which the profile stays above some rational `q > c`,
then `g` is a weak derivative of `v` on the whole axial level interval at height `c`.

A test function supported in that interval has compact support, so it is supported in some
`(s,t)` with rational endpoints whose closure stays inside; on that compact interval the
(continuous) profile attains a minimum `> c`, which supplies the rational `q`. -/
theorem hasWeakDeriv_of_rat_subinterval (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    {v g : ℝ → ℝ} {c : ℝ}
    (h : ∀ s t q : ℚ, ((s : ℝ) < (t : ℝ)) →
      Icc (s : ℝ) (t : ℝ) ⊆ levelSet Cm Cp L R (q : ℝ) → c < (q : ℝ) →
      RobinCaps.Sobolev.HasWeakDeriv (s : ℝ) (t : ℝ) v g) :
    RobinCaps.Sobolev.HasWeakDeriv (levelInf Cm Cp L R c) (levelSup Cm Cp L R c) v g := by
  intro φ hφ hφc hφs
  rcases eq_empty_or_nonempty (tsupport φ) with hemp | hne
  · have h0 : φ = fun _ => (0 : ℝ) := by
      funext x
      exact image_eq_zero_of_notMem_tsupport (by rw [hemp]; exact notMem_empty x)
    subst h0
    simp
  · obtain ⟨α, hα, hαmin⟩ :=
      IsCompact.exists_isMinOn (f := fun x : ℝ => x) hφc hne continuous_id'.continuousOn
    obtain ⟨β, hβ, hβmax⟩ :=
      IsCompact.exists_isMaxOn (f := fun x : ℝ => x) hφc hne continuous_id'.continuousOn
    have hαle : ∀ x ∈ tsupport φ, α ≤ x := fun x hx => isMinOn_iff.1 hαmin x hx
    have hβge : ∀ x ∈ tsupport φ, x ≤ β := fun x hx => isMaxOn_iff.1 hβmax x hx
    have hαb := hφs hα
    have hβb := hφs hβ
    obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn hαb.1
    obtain ⟨t, ht1, ht2⟩ := exists_rat_btwn hβb.2
    have hαβ : α ≤ β := hαle β hβ
    have hst : (s : ℝ) < (t : ℝ) := by linarith
    have hIcclev : Icc (s : ℝ) (t : ℝ) ⊆ levelSet Cm Cp L R c := by
      rw [levelSet_eq_Ioo hR hL]
      exact Icc_subset_Ioo hs1 ht2
    have hIccne : (Icc (s : ℝ) (t : ℝ)).Nonempty := nonempty_Icc.2 hst.le
    have hcont : ContinuousOn (profile Cm Cp L R) (Icc (s : ℝ) (t : ℝ)) :=
      (continuousOn_profile hR hL).mono fun x hx => (hIcclev hx).1
    obtain ⟨x₀, hx₀, hx₀min⟩ := IsCompact.exists_isMinOn isCompact_Icc hIccne hcont
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (hIcclev hx₀).2
    have hIccq : Icc (s : ℝ) (t : ℝ) ⊆ levelSet Cm Cp L R (q : ℝ) := fun x hx =>
      ⟨(hIcclev hx).1, lt_of_lt_of_le hq2 (isMinOn_iff.1 hx₀min x hx)⟩
    have hφsub : tsupport φ ⊆ Ioo (s : ℝ) (t : ℝ) := fun x hx =>
      ⟨lt_of_lt_of_le hs2 (hαle x hx), lt_of_le_of_lt (hβge x hx) ht1⟩
    have hident := h s t q hst hIccq hq1 φ hφ hφc hφsub
    rw [setIntegral_mul_deriv_eq_integral hφs, setIntegral_mul_test_eq_integral hφs,
      ← setIntegral_mul_deriv_eq_integral hφsub, ← setIntegral_mul_test_eq_integral hφsub]
    exact hident

/-- **Deliverable 3 (axial ACL on the thin domain).**  For almost every transverse coordinate
`z` with `‖z‖ < R`, the axial slice `x ↦ u(x,z)` has `x ↦ (∂ₓ u)(x,z)` as a weak derivative on
the whole axial slice `(aZ z, bZ z)` of `Ω_R`. -/
theorem sliceACL_axial_thin (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) R)),
      RobinCaps.Sobolev.HasWeakDeriv (aZ Cm Cp L R z) (bZ Cm Cp L R z)
        (fun x => u.toFun (x, z)) (fun x => u.gx (x, z)) := by
  have key : ∀ k : ℚ × ℚ × ℚ,
      ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) R)),
        z ∈ ball (0 : EuclideanSpace ℝ (Fin m)) ((k.2.2 : ℚ) : ℝ) →
        ((k.1 : ℝ) < (k.2.1 : ℝ)) →
        Icc ((k.1 : ℚ) : ℝ) ((k.2.1 : ℚ) : ℝ) ⊆ levelSet Cm Cp L R ((k.2.2 : ℚ) : ℝ) →
        RobinCaps.Sobolev.HasWeakDeriv ((k.1 : ℚ) : ℝ) ((k.2.1 : ℚ) : ℝ)
          (fun x => u.toFun (x, z)) (fun x => u.gx (x, z)) := by
    intro k
    by_cases hk : ((k.1 : ℝ) < (k.2.1 : ℝ)) ∧
        Icc ((k.1 : ℚ) : ℝ) ((k.2.1 : ℚ) : ℝ) ⊆ levelSet Cm Cp L R ((k.2.2 : ℚ) : ℝ)
    · filter_upwards [ae_imp_of_ae_restrict measurableSet_ball _
        (sliceACL_axial_sub u hk.1 hk.2)] with z hz hzb _ _
      exact hz hzb
    · filter_upwards with z _ h1 h2
      exact absurd ⟨h1, h2⟩ hk
  filter_upwards [ae_all_iff.2 key] with z hz
  refine hasWeakDeriv_of_rat_subinterval hR hL fun s t q hst hIcc hq => ?_
  exact hz (s, t, q) (mem_ball_zero_iff.2 hq) hst hIcc

/-- **The `SliceACLAxial` target of `RobinCaps/ThinDomain/H1P.lean` for the thin domain.** -/
theorem sliceACLAxial_thin (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) : SliceACLAxial (thinDomain Cm Cp L R) u := by
  have h := sliceACL_axial_thin hR hL u
  rw [ae_restrict_iff' measurableSet_ball] at h
  filter_upwards [h] with z hz
  by_cases hzR : z ∈ ball (0 : EuclideanSpace ℝ (Fin m)) R
  · rw [thinDomain_axialSlice hR hL]
    exact hz hzR
  · rw [thinDomain_axialSlice_eq_empty hR hL
      (not_lt.1 fun hc => hzR (mem_ball_zero_iff.2 hc))]
    intro φ hφ hφc hφs
    simp

end

end RobinCaps.ThinDomain
