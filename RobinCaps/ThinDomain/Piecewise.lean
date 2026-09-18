import Mathlib
import RobinCaps.ThinDomain.H1P
import RobinCaps.Transverse.OneDim

/-!
# U-SOB-PW: continuous, piecewise `C¹` functions are weak `H¹` functions on the thin domain

The trial functions of the manuscript (`eq:trial-extension`) are built by gluing a bulk profile
`F(x)ψ_R(z)` to the cap pieces **across the interface slices** `{x = c_i}`.  Such a function is
continuous on the thin domain and `C¹` on each of the finitely many pieces cut out by the axial
hyperplanes `{x = c}`, `c ∈ S`, but it is *not* `C¹` across the interfaces, so
`RobinCaps.ThinDomain.hasWeakGradP_classical` does not apply to it.

This file supplies the missing sufficient condition:

* `ftc_piecewise`: the fundamental theorem of calculus on `[a,b]` for a function that is merely
  continuous on `[a,b]` and differentiable off a finite set (proved by induction on the number
  of exceptional points; the boundary terms telescope by continuity).
* `integral_deriv_eq_zero_of_piecewise`, `integral_mul_deriv_piecewise`: the resulting
  one-dimensional integration-by-parts identity `∫ f φ' = - ∫ g φ` on all of `ℝ`.
* `gluedProd`, `continuous_gluedProd`: the product `u · φ` extended by zero off `Ω` is globally
  continuous when `tsupport φ ⊆ Ω` and `u` is continuous on the open set `Ω` — this is what makes
  the slice arguments work without any control of `u` near `∂Ω`.
* `integral_axial_piecewise_eq_zero`, `integral_transverse_piecewise_eq_zero`: the two halves of
  the integration by parts on `CapSpace m`, obtained exactly as in
  `RobinCaps/ThinDomain/H1P.lean` — Fubini (`Measure.volume_eq_prod` is `rfl`) reduces the axial
  direction to the piecewise one-dimensional FTC on each line `ℝ × {z}`, and the transverse
  direction to `RobinCaps.Sobolev.Weak.integral_fderiv_single_eq_zero` on each slice `{x} × ℝᵐ`
  with `x ∉ S` (the interfaces form a null set of axial coordinates).
* `hasWeakGradP_of_piecewise`: the main theorem.  If `Ω` is open, `u` is continuous on `Ω`,
  `C¹` on `Ω' = Ω \ {p | p.1 ∈ S}` and has bounded classical derivatives there, then
  `HasWeakGradP Ω u (dxP u) (gradZP u)`.  The values of `dxP u` and `gradZP u` on the null set
  of interfaces are irrelevant: the proof replaces them throughout by the bounded measurable
  stand-ins `Ω'.indicator (dxP u)` and `Ω'.indicator ((gradZP u) ·ᵢ)`.
* `H1P.ofPiecewise`: the bundled `H1P Ω` element, for bounded `Ω` and bounded `u`.

Everything is proved; there is no `sorry`, `axiom`, `admit` or `native_decide`.
-/

open MeasureTheory Set Filter

open scoped ContDiff ENNReal Topology

namespace RobinCaps.ThinDomain

noncomputable section

/-! ### One-dimensional fundamental theorem of calculus with finitely many bad points -/

/-- **FTC with finitely many exceptional points.**  If `w` is continuous on `[a,b]` and has
derivative `w'` at every point of `(a,b)` outside the finite set `S`, and `w'` is interval
integrable, then `∫_a^b w' = w b - w a`.

Proved by induction on a bound for the (finite) number of exceptional points: each point of `S`
inside `(a,b)` splits the interval into two pieces on which the induction hypothesis applies, and
the boundary values telescope because `w` is continuous. -/
theorem ftc_piecewise_aux :
    ∀ (n : ℕ) (S : Finset ℝ), S.card ≤ n → ∀ (w w' : ℝ → ℝ) (a b : ℝ), a ≤ b →
      ContinuousOn w (Icc a b) → (∀ x ∈ Ioo a b, x ∉ S → HasDerivAt w (w' x) x) →
      IntervalIntegrable w' volume a b → (∫ x in a..b, w' x) = w b - w a := by
  intro n
  induction n with
  | zero =>
    intro S hS w w' a b hab hcont hd hint
    have hS0 : S = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hS)
    subst hS0
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont
      (fun x hx => hd x hx (by simp)) hint
  | succ n ih =>
    intro S hS w w' a b hab hcont hd hint
    rcases S.eq_empty_or_nonempty with hSe | hSne
    · subst hSe
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont
        (fun x hx => hd x hx (by simp)) hint
    obtain ⟨c, hc⟩ := hSne
    have hTcard : (S.erase c).card ≤ n := by
      have h1 : (S.erase c).card = S.card - 1 := Finset.card_erase_of_mem hc
      have h2 : 1 ≤ S.card := Finset.card_pos.2 ⟨c, hc⟩
      omega
    by_cases hcmem : c ∈ Ioo a b
    · obtain ⟨hac, hcb⟩ := hcmem
      have hac' : a ≤ c := hac.le
      have hcb' : c ≤ b := hcb.le
      have hsub1 : uIcc a c ⊆ uIcc a b := by
        rw [uIcc_of_le hac', uIcc_of_le hab]; exact Icc_subset_Icc le_rfl hcb'
      have hsub2 : uIcc c b ⊆ uIcc a b := by
        rw [uIcc_of_le hcb', uIcc_of_le hab]; exact Icc_subset_Icc hac' le_rfl
      have hint1 : IntervalIntegrable w' volume a c := hint.mono_set hsub1
      have hint2 : IntervalIntegrable w' volume c b := hint.mono_set hsub2
      have h1 : (∫ x in a..c, w' x) = w c - w a := by
        refine ih (S.erase c) hTcard w w' a c hac'
          (hcont.mono (Icc_subset_Icc le_rfl hcb')) (fun x hx hxT => ?_) hint1
        refine hd x ⟨hx.1, hx.2.trans hcb⟩ (fun hxS => ?_)
        exact hxT (Finset.mem_erase.2 ⟨ne_of_lt hx.2, hxS⟩)
      have h2 : (∫ x in c..b, w' x) = w b - w c := by
        refine ih (S.erase c) hTcard w w' c b hcb'
          (hcont.mono (Icc_subset_Icc hac' le_rfl)) (fun x hx hxT => ?_) hint2
        refine hd x ⟨hac.trans hx.1, hx.2⟩ (fun hxS => ?_)
        exact hxT (Finset.mem_erase.2 ⟨(ne_of_lt hx.1).symm, hxS⟩)
      have hsplit := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
      rw [h1, h2] at hsplit
      rw [← hsplit]; ring
    · refine ih (S.erase c) hTcard w w' a b hab hcont (fun x hx hxT => ?_) hint
      refine hd x hx (fun hxS => ?_)
      rcases eq_or_ne x c with rfl | hne
      · exact hcmem hx
      · exact hxT (Finset.mem_erase.2 ⟨hne, hxS⟩)

/-- **FTC with finitely many exceptional points** (usable form). -/
theorem ftc_piecewise (S : Finset ℝ) (w w' : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn w (Icc a b))
    (hd : ∀ x ∈ Ioo a b, x ∉ S → HasDerivAt w (w' x) x)
    (hint : IntervalIntegrable w' volume a b) :
    (∫ x in a..b, w' x) = w b - w a :=
  ftc_piecewise_aux S.card S le_rfl w w' a b hab hcont hd hint

/-- A compactly supported continuous function whose derivative exists off a finite set has
`∫ w' = 0`.  This is the piecewise version of
`RobinCaps.ThinDomain.integral_deriv_eq_zero_of_compactSupport`. -/
theorem integral_deriv_eq_zero_of_piecewise (S : Finset ℝ) (w w' : ℝ → ℝ)
    (hwc : HasCompactSupport w) (hw : Continuous w)
    (hd : ∀ x, x ∉ S → HasDerivAt w (w' x) x)
    (hint : ∀ a b : ℝ, IntervalIntegrable w' volume a b) :
    (∫ x, w' x) = 0 := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hwc.isBounded
  set R : ℝ := max r 0 + 1 with hRdef
  have hrR : r < R := by
    have : r ≤ max r 0 := le_max_left _ _
    linarith
  have hR0 : (0 : ℝ) < R := by
    have : (0 : ℝ) ≤ max r 0 := le_max_right _ _
    linarith
  have hsupp : ∀ x : ℝ, x ∉ Icc (-R) R → x ∉ tsupport w := by
    intro x hx hmem
    have h1 : |x| ≤ r := by
      simpa [Real.norm_eq_abs, mem_closedBall_zero_iff] using hr hmem
    exact hx ⟨by cases abs_le.1 h1 with | intro h2 _ => linarith,
      by cases abs_le.1 h1 with | intro _ h3 => linarith⟩
  -- off the support (and off `S`), the derivative vanishes
  have hvan : ∀ x : ℝ, x ∉ S → x ∉ Icc (-R) R → w' x = 0 := by
    intro x hxS hx
    have hx' : x ∉ tsupport w := hsupp x hx
    have hnhds : ∀ᶠ y in nhds x, w y = 0 := by
      filter_upwards [(isOpen_compl_iff.2 (isClosed_tsupport w)).mem_nhds hx'] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    have h0 : HasDerivAt w 0 x :=
      (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hnhds
    exact (hd x hxS).unique h0
  -- hence `w'` agrees a.e. with its restriction to `[-R, R]`
  have hae : w' =ᵐ[volume] (Icc (-R) R).indicator w' := by
    have hnull : (volume : Measure ℝ) (S : Set ℝ) = 0 := S.finite_toSet.measure_zero _
    refine ae_iff.2 (measure_mono_null (fun x hx => ?_) hnull)
    simp only [mem_setOf_eq] at hx
    by_contra hxS
    by_cases hmem : x ∈ Icc (-R) R
    · exact hx (Set.indicator_of_mem hmem w').symm
    · rw [Set.indicator_of_notMem hmem] at hx
      exact hx (hvan x (by simpa using hxS) hmem)
  have hIcc : (∫ x, w' x) = ∫ x in Icc (-R) R, w' x := by
    rw [integral_congr_ae hae, integral_indicator measurableSet_Icc]
  rw [hIcc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : (-R : ℝ) ≤ R),
    ftc_piecewise S w w' (by linarith : (-R : ℝ) ≤ R) hw.continuousOn
      (fun x _ hxS => hd x hxS) (hint _ _)]
  have hbig : ∀ x : ℝ, r < |x| → x ∉ tsupport w := by
    intro x hx hmem
    have h1 : |x| ≤ r := by
      simpa [Real.norm_eq_abs, mem_closedBall_zero_iff] using hr hmem
    linarith
  have h1 : w R = 0 :=
    image_eq_zero_of_notMem_tsupport (hbig R (by rw [abs_of_pos hR0]; exact hrR))
  have h2 : w (-R) = 0 :=
    image_eq_zero_of_notMem_tsupport (hbig (-R) (by rw [abs_neg, abs_of_pos hR0]; exact hrR))
  rw [h1, h2, sub_zero]

/-- **One-dimensional integration by parts for a continuous, piecewise `C¹` function.**

If `f : ℝ → ℝ` is continuous, has the derivative `g x` at every `x` outside the finite set `S`
(the interface abscissae), and `g` is measurable and bounded, then for every compactly supported
`C¹` test function `φ`

`∫ f · φ' = - ∫ g · φ`.

The values of `g` on `S` are irrelevant (`S` is a null set). -/
theorem integral_mul_deriv_piecewise (S : Finset ℝ) (f g φ : ℝ → ℝ)
    (hf : Continuous f) (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hfd : ∀ x, x ∉ S → HasDerivAt f (g x) x)
    (hgm : Measurable g) {M : ℝ} (hgb : ∀ x, |g x| ≤ M) :
    (∫ x, f x * deriv φ x) = - ∫ x, g x * φ x := by
  have hφcont : Continuous φ := hφ.continuous
  have hφ' : Continuous (deriv φ) := hφ.continuous_deriv_one
  -- the two pieces of the integrand are integrable
  have hIφ : Integrable φ volume := hφcont.integrable_of_hasCompactSupport hφc
  have hI1 : Integrable (fun x => g x * φ x) volume :=
    hIφ.bdd_mul hgm.aestronglyMeasurable
      (.of_forall fun x => by rw [Real.norm_eq_abs]; exact hgb x)
  have hI2 : Integrable (fun x => f x * deriv φ x) volume :=
    (hf.mul hφ').integrable_of_hasCompactSupport (hφc.deriv.mul_left)
  -- the product `f · φ` is continuous, compactly supported, and piecewise differentiable
  have hzero : (∫ x, (g x * φ x + f x * deriv φ x)) = 0 := by
    refine integral_deriv_eq_zero_of_piecewise S (fun x => f x * φ x) _ hφc.mul_left
      (hf.mul hφcont) (fun x hx => ?_) (fun a b => ?_)
    · exact (hfd x hx).mul ((hφ.differentiable le_rfl).differentiableAt.hasDerivAt)
    · have hsum : Integrable (fun x => g x * φ x + f x * deriv φ x) volume := hI1.add hI2
      exact hsum.intervalIntegrable
  rw [integral_add hI1 hI2] at hzero
  linarith

/-! ### The glued product `u · φ` -/

variable {m : ℕ}

/-- The product `u · φ` extended by zero outside `Ω`.  When `tsupport φ ⊆ Ω` and `u` is
continuous on the open set `Ω`, this is a *globally* continuous, compactly supported function
even though `u` itself need not be continuous (or even defined in any reasonable way) off `Ω`. -/
def gluedProd (Ω : Set (CapSpace m)) (u φ : CapSpace m → ℝ) : CapSpace m → ℝ :=
  Ω.indicator fun p => u p * φ p

theorem gluedProd_of_mem {Ω : Set (CapSpace m)} {u φ : CapSpace m → ℝ} {p : CapSpace m}
    (hp : p ∈ Ω) : gluedProd Ω u φ p = u p * φ p := Set.indicator_of_mem hp _

theorem gluedProd_of_notMem_tsupport {Ω : Set (CapSpace m)} {u φ : CapSpace m → ℝ}
    {p : CapSpace m} (hp : p ∉ tsupport φ) : gluedProd Ω u φ p = 0 := by
  unfold gluedProd
  by_cases hpΩ : p ∈ Ω
  · rw [Set.indicator_of_mem hpΩ, image_eq_zero_of_notMem_tsupport hp, mul_zero]
  · rw [Set.indicator_of_notMem hpΩ]

theorem hasCompactSupport_gluedProd {Ω : Set (CapSpace m)} (u : CapSpace m → ℝ)
    {φ : CapSpace m → ℝ} (hφc : HasCompactSupport φ) : HasCompactSupport (gluedProd Ω u φ) :=
  HasCompactSupport.intro hφc fun _ hp => gluedProd_of_notMem_tsupport hp

theorem continuous_gluedProd {Ω : Set (CapSpace m)} {u φ : CapSpace m → ℝ} (hΩ : IsOpen Ω)
    (hu : ContinuousOn u Ω) (hφ : Continuous φ) (hφs : tsupport φ ⊆ Ω) :
    Continuous (gluedProd Ω u φ) := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : p ∈ Ω
  · refine ContinuousOn.continuousAt ?_ (hΩ.mem_nhds hp)
    exact (hu.mul hφ.continuousOn).congr fun q hq => gluedProd_of_mem hq
  · have hpt : p ∉ tsupport φ := fun h => hp (hφs h)
    have hev : gluedProd Ω u φ =ᶠ[nhds p] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_compl_iff.2 (isClosed_tsupport φ)).mem_nhds hpt] with q hq
      exact gluedProd_of_notMem_tsupport hq
    rw [ContinuousAt, gluedProd_of_notMem_tsupport hpt]
    exact Filter.Tendsto.congr' hev.symm tendsto_const_nhds

/-! ### The interface hyperplanes -/

/-- The union of the interface hyperplanes `{x = c}`, `c ∈ S`, is closed. -/
theorem isClosed_interfaces (S : Finset ℝ) :
    IsClosed {p : CapSpace m | p.1 ∈ S} := by
  have h : {p : CapSpace m | p.1 ∈ S} = Prod.fst ⁻¹' (S : Set ℝ) := rfl
  rw [h]
  exact (S.finite_toSet.isClosed).preimage continuous_fst

/-- The union of the interface hyperplanes is a Lebesgue null set of `CapSpace m`. -/
theorem volume_interfaces_eq_zero (S : Finset ℝ) :
    volume {p : CapSpace m | p.1 ∈ S} = 0 := by
  have h : {p : CapSpace m | p.1 ∈ S}
      = (S : Set ℝ) ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin m))) := by
    ext p; simp
  rw [h, Measure.volume_eq_prod, Measure.prod_prod, S.finite_toSet.measure_zero, zero_mul]

/-- The axial slice of a compactly supported function has compact support. -/
theorem hasCompactSupport_axialSlice {f : CapSpace m → ℝ} (hf : HasCompactSupport f)
    (z : EuclideanSpace ℝ (Fin m)) : HasCompactSupport fun t : ℝ => f (t, z) := by
  refine HasCompactSupport.intro ((hf : IsCompact (tsupport f)).image continuous_fst) ?_
  intro t ht
  exact image_eq_zero_of_notMem_tsupport fun hm => ht ⟨(t, z), hm, rfl⟩

/-- The transverse slice of a compactly supported function has compact support. -/
theorem hasCompactSupport_transverseSlice {f : CapSpace m → ℝ} (hf : HasCompactSupport f)
    (x : ℝ) : HasCompactSupport fun w : EuclideanSpace ℝ (Fin m) => f (x, w) := by
  refine HasCompactSupport.intro ((hf : IsCompact (tsupport f)).image continuous_snd) ?_
  intro w hw
  exact image_eq_zero_of_notMem_tsupport fun hm => hw ⟨(x, w), hm, rfl⟩

/-- The total support of a directional derivative of `φ` is contained in that of `φ`. -/
theorem tsupport_fderiv_apply_subset (φ : CapSpace m → ℝ) (v : CapSpace m) :
    tsupport (fun p => fderiv ℝ φ p v) ⊆ tsupport φ := by
  refine closure_minimal (fun p hp => ?_) (isClosed_tsupport φ)
  refine support_fderiv_subset ℝ (Function.mem_support.2 fun h => ?_)
  exact (Function.mem_support.1 hp) (by rw [h]; simp)

/-- `p ↦ u p · ∂_v φ p` is globally continuous as soon as `u` is continuous on the open set `Ω`
containing `tsupport φ`: off `tsupport φ` the factor `∂_vφ` vanishes. -/
theorem continuous_mul_fderiv_apply {Ω : Set (CapSpace m)} {u φ : CapSpace m → ℝ}
    (hΩ : IsOpen Ω) (hu : ContinuousOn u Ω) (hφ : ContDiff ℝ 1 φ) (hφs : tsupport φ ⊆ Ω)
    (v : CapSpace m) : Continuous fun p => u p * fderiv ℝ φ p v := by
  have hψ : Continuous fun p : CapSpace m => fderiv ℝ φ p v :=
    (hφ.continuous_fderiv le_rfl).clm_apply continuous_const
  have heq : (fun p => u p * fderiv ℝ φ p v)
      = gluedProd Ω u fun p => fderiv ℝ φ p v := by
    funext p
    by_cases hp : p ∈ Ω
    · rw [gluedProd_of_mem hp]
    · have hpt : p ∉ tsupport φ := fun h => hp (hφs h)
      have h1 : fderiv ℝ φ p = 0 :=
        Function.notMem_support.1 fun h => hpt (support_fderiv_subset ℝ h)
      have h2 : p ∉ tsupport fun q : CapSpace m => fderiv ℝ φ q v :=
        fun h => hpt (tsupport_fderiv_apply_subset φ v h)
      rw [gluedProd_of_notMem_tsupport h2, h1]
      simp
  rw [heq]
  exact continuous_gluedProd hΩ hu hψ ((tsupport_fderiv_apply_subset φ v).trans hφs)

/-- `p ↦ u p · ∂_vφ p` has compact support. -/
theorem hasCompactSupport_mul_fderiv_apply {u φ : CapSpace m → ℝ} (hφc : HasCompactSupport φ)
    (v : CapSpace m) : HasCompactSupport fun p => u p * fderiv ℝ φ p v :=
  HasCompactSupport.intro hφc fun p hp => by
    have h1 : fderiv ℝ φ p = 0 :=
      Function.notMem_support.1 fun h => hp (support_fderiv_subset ℝ h)
    rw [h1]; simp

/-! ### The axial direction -/

/-- **The axial integration-by-parts identity for a continuous, piecewise `C¹` function.**

Here `g` is a bounded measurable stand-in for `∂ₓ u`, equal to it on the punctured domain
`Ω' = Ω \ {x ∈ S}` and zero off `Ω'`. -/
theorem integral_axial_piecewise_eq_zero {Ω : Set (CapSpace m)} (hΩ : IsOpen Ω) {S : Finset ℝ}
    {u : CapSpace m → ℝ} (hu : ContinuousOn u Ω)
    (hu' : ContDiffOn ℝ 1 u (Ω \ {p : CapSpace m | p.1 ∈ S}))
    {g : CapSpace m → ℝ} {M : ℝ} (hgm : Measurable g) (hgb : ∀ p, |g p| ≤ M)
    (hgin : ∀ p ∈ Ω \ {p : CapSpace m | p.1 ∈ S}, g p = dxP u p)
    (hgout : ∀ p, p ∉ Ω → g p = 0)
    {φ : CapSpace m → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ω) :
    (∫ p, (u p * fderiv ℝ φ p ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))) + g p * φ p)) = 0 := by
  have hΩ' : IsOpen (Ω \ {p : CapSpace m | p.1 ∈ S}) := hΩ.sdiff (isClosed_interfaces S)
  set v : CapSpace m := ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))) with hvdef
  set W : CapSpace m → ℝ := gluedProd Ω u φ with hWdef
  have hWc : Continuous W := continuous_gluedProd hΩ hu hφ.continuous hφs
  have hWcs' : HasCompactSupport W := hasCompactSupport_gluedProd u hφc
  set F : CapSpace m → ℝ := fun p => u p * fderiv ℝ φ p v + g p * φ p with hFdef
  -- integrability of the two pieces
  have hPc : Continuous fun p => u p * fderiv ℝ φ p v :=
    continuous_mul_fderiv_apply hΩ hu hφ hφs v
  have hPs : HasCompactSupport fun p : CapSpace m => u p * fderiv ℝ φ p v :=
    hasCompactSupport_mul_fderiv_apply hφc v
  have hIP : Integrable (fun p : CapSpace m => u p * fderiv ℝ φ p v) volume :=
    hPc.integrable_of_hasCompactSupport hPs
  have hIφ : Integrable φ volume := hφ.continuous.integrable_of_hasCompactSupport hφc
  have hIQ : Integrable (fun p : CapSpace m => g p * φ p) volume :=
    hIφ.bdd_mul hgm.aestronglyMeasurable
      (.of_forall fun p => by rw [Real.norm_eq_abs]; exact hgb p)
  have hIF : Integrable F volume := hIP.add hIQ
  -- slice-wise vanishing
  have hslice : ∀ z : EuclideanSpace ℝ (Fin m), (∫ x : ℝ, F (x, z)) = 0 := by
    intro z
    have hemb : Continuous fun t : ℝ => ((t, z) : CapSpace m) :=
      continuous_id.prodMk continuous_const
    have hembm : Measurable fun t : ℝ => ((t, z) : CapSpace m) := hemb.measurable
    refine integral_deriv_eq_zero_of_piecewise S (fun t => W (t, z)) (fun t => F (t, z))
      (hasCompactSupport_axialSlice hWcs' z) (hWc.comp hemb)
      (fun x hxS => ?_) (fun a b => ?_)
    · -- the piecewise derivative
      by_cases hmem : ((x, z) : CapSpace m) ∈ Ω
      · have hmem' : ((x, z) : CapSpace m) ∈ Ω \ {p : CapSpace m | p.1 ∈ S} :=
          ⟨hmem, by simpa using hxS⟩
        have hdiff : DifferentiableAt ℝ u ((x, z) : CapSpace m) :=
          (hu'.contDiffAt (hΩ'.mem_nhds hmem')).differentiableAt le_rfl
        have hline : HasDerivAt (fun t : ℝ => ((t, z) : CapSpace m)) v x :=
          (hasDerivAt_id x).prodMk (hasDerivAt_const x z)
        have hu2 : HasDerivAt (fun t : ℝ => u (t, z)) (fderiv ℝ u (x, z) v) x := by
          simpa [Function.comp_def] using hdiff.hasFDerivAt.comp_hasDerivAt x hline
        have hφ2 : HasDerivAt (fun t : ℝ => φ (t, z)) (fderiv ℝ φ (x, z) v) x := by
          simpa [Function.comp_def] using
            (hφ.differentiable le_rfl (x, z)).hasFDerivAt.comp_hasDerivAt x hline
        have hev : (fun t : ℝ => W (t, z)) =ᶠ[nhds x] fun t : ℝ => u (t, z) * φ (t, z) := by
          have hopen : IsOpen {t : ℝ | ((t, z) : CapSpace m) ∈ Ω} := hΩ.preimage hemb
          filter_upwards [hopen.mem_nhds hmem] with t ht
          exact gluedProd_of_mem ht
        have hres := (hu2.mul hφ2).congr_of_eventuallyEq hev
        show HasDerivAt (fun t : ℝ => W (t, z)) (F (x, z)) x
        have hg1 : g ((x, z) : CapSpace m) = fderiv ℝ u (x, z) v := by
          rw [hgin _ hmem', hvdef]; rfl
        have hval : F (x, z)
            = fderiv ℝ u (x, z) v * φ (x, z) + u (x, z) * fderiv ℝ φ (x, z) v := by
          simp only [hFdef, hg1]
          ring
        rw [hval]
        exact hres
      · have hpt : ((x, z) : CapSpace m) ∉ tsupport φ := fun h => hmem (hφs h)
        have hopen : IsOpen {t : ℝ | ((t, z) : CapSpace m) ∉ tsupport φ} :=
          (isOpen_compl_iff.2 (isClosed_tsupport φ)).preimage hemb
        have hev : (fun t : ℝ => W (t, z)) =ᶠ[nhds x] fun _ : ℝ => (0 : ℝ) := by
          filter_upwards [hopen.mem_nhds hpt] with t ht
          exact gluedProd_of_notMem_tsupport ht
        show HasDerivAt (fun t : ℝ => W (t, z)) (F (x, z)) x
        have hF0 : F (x, z) = 0 := by
          have h1 : fderiv ℝ φ ((x, z) : CapSpace m) = 0 :=
            Function.notMem_support.1 fun h => hpt (support_fderiv_subset ℝ h)
          have h2 : g ((x, z) : CapSpace m) = 0 := hgout _ hmem
          simp only [hFdef, h1, h2]
          simp
        rw [hF0]
        exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hev
    · -- interval integrability of the slice
      have hcont1 : Continuous fun t : ℝ => u (t, z) * fderiv ℝ φ ((t, z) : CapSpace m) v :=
        hPc.comp hemb
      have h1 : Integrable (fun t : ℝ => u (t, z) * fderiv ℝ φ ((t, z) : CapSpace m) v) volume :=
        hcont1.integrable_of_hasCompactSupport (hasCompactSupport_axialSlice hPs z)
      have h2 : Integrable (fun t : ℝ => g ((t, z) : CapSpace m) * φ (t, z)) volume := by
        have hcont2 : Continuous fun t : ℝ => φ ((t, z) : CapSpace m) := hφ.continuous.comp hemb
        have hφz : Integrable (fun t : ℝ => φ ((t, z) : CapSpace m)) volume :=
          hcont2.integrable_of_hasCompactSupport (hasCompactSupport_axialSlice hφc z)
        exact hφz.bdd_mul (hgm.comp hembm).aestronglyMeasurable
          (.of_forall fun t => by rw [Real.norm_eq_abs]; exact hgb _)
      have : Integrable (fun t : ℝ => F (t, z)) volume := h1.add h2
      exact this.intervalIntegrable
  -- Fubini
  have hIF' : Integrable F
      ((volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin m)))) := by
    rwa [← Measure.volume_eq_prod]
  calc (∫ p, F p)
      = ∫ p, F p ∂((volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin m)))) := by
        rw [← Measure.volume_eq_prod]
    _ = ∫ z, ∫ x, F (x, z) := by rw [integral_prod_symm _ hIF']
    _ = 0 := by simp [hslice]

/-! ### The transverse directions -/

/-- The transverse slice of `fderiv`: `∂_{z i}` of `u(x, ·)` is `∂_{(0, e i)}` of `u`. -/
theorem fderiv_transverseSlice_apply {u : CapSpace m → ℝ} {x : ℝ}
    {w : EuclideanSpace ℝ (Fin m)} (h : DifferentiableAt ℝ u (x, w)) :
    HasFDerivAt (fun v : EuclideanSpace ℝ (Fin m) => u (x, v))
      ((fderiv ℝ u (x, w)).comp
        (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin m)))) w :=
  h.hasFDerivAt.comp w (hasFDerivAt_prodMk_right x w)

/-- **The transverse integration-by-parts identity for a continuous, piecewise `C¹` function.**

Here `g` is a bounded measurable stand-in for `(∇_z u)_i`, equal to it on the punctured domain
`Ω' = Ω \ {x ∈ S}` and zero off `Ω`. -/
theorem integral_transverse_piecewise_eq_zero {Ω : Set (CapSpace m)} (hΩ : IsOpen Ω)
    {S : Finset ℝ} {u : CapSpace m → ℝ} (hu : ContinuousOn u Ω)
    (hu' : ContDiffOn ℝ 1 u (Ω \ {p : CapSpace m | p.1 ∈ S}))
    {g : CapSpace m → ℝ} {M : ℝ} (hgm : Measurable g) (hgb : ∀ p, |g p| ≤ M)
    (i : Fin m)
    (hgin : ∀ p ∈ Ω \ {p : CapSpace m | p.1 ∈ S}, g p = gradZP u p i)
    (hgout : ∀ p, p ∉ Ω → g p = 0)
    {φ : CapSpace m → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ω) :
    (∫ p, (u p * fderiv ℝ φ p ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)) + g p * φ p)) = 0 := by
  have hΩ' : IsOpen (Ω \ {p : CapSpace m | p.1 ∈ S}) := hΩ.sdiff (isClosed_interfaces S)
  set v : CapSpace m := ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)) with hvdef
  set W : CapSpace m → ℝ := gluedProd Ω u φ with hWdef
  have hWc : Continuous W := continuous_gluedProd hΩ hu hφ.continuous hφs
  have hWcs : HasCompactSupport W := hasCompactSupport_gluedProd u hφc
  set F : CapSpace m → ℝ := fun p => u p * fderiv ℝ φ p v + g p * φ p with hFdef
  have hPc : Continuous fun p => u p * fderiv ℝ φ p v :=
    continuous_mul_fderiv_apply hΩ hu hφ hφs v
  have hPs : HasCompactSupport fun p : CapSpace m => u p * fderiv ℝ φ p v :=
    hasCompactSupport_mul_fderiv_apply hφc v
  have hIP : Integrable (fun p : CapSpace m => u p * fderiv ℝ φ p v) volume :=
    hPc.integrable_of_hasCompactSupport hPs
  have hIφ : Integrable φ volume := hφ.continuous.integrable_of_hasCompactSupport hφc
  have hIQ : Integrable (fun p : CapSpace m => g p * φ p) volume :=
    hIφ.bdd_mul hgm.aestronglyMeasurable
      (.of_forall fun p => by rw [Real.norm_eq_abs]; exact hgb p)
  have hIF : Integrable F volume := hIP.add hIQ
  -- slices over the axial coordinate, away from the interfaces
  have hmain : ∀ x : ℝ, x ∉ S → (∫ z : EuclideanSpace ℝ (Fin m), F (x, z)) = 0 := by
    intro x hxS
    have hemb : Continuous fun w : EuclideanSpace ℝ (Fin m) => ((x, w) : CapSpace m) :=
      continuous_const.prodMk continuous_id
    have hφslice : ContDiff ℝ 1 fun w : EuclideanSpace ℝ (Fin m) => φ (x, w) :=
      hφ.comp (contDiff_const.prodMk contDiff_id)
    -- the glued slice is `C¹`
    have hopenΩ : IsOpen {w : EuclideanSpace ℝ (Fin m) | ((x, w) : CapSpace m) ∈ Ω} :=
      hΩ.preimage hemb
    have hopenΩ' : IsOpen {w : EuclideanSpace ℝ (Fin m) |
        ((x, w) : CapSpace m) ∈ Ω \ {p : CapSpace m | p.1 ∈ S}} := hΩ'.preimage hemb
    have huslice : ContDiffOn ℝ 1 (fun w : EuclideanSpace ℝ (Fin m) => u (x, w))
        {w : EuclideanSpace ℝ (Fin m) | ((x, w) : CapSpace m)
          ∈ Ω \ {p : CapSpace m | p.1 ∈ S}} :=
      hu'.comp (contDiff_const.prodMk contDiff_id).contDiffOn fun w hw => hw
    have hev : ∀ w : EuclideanSpace ℝ (Fin m), ((x, w) : CapSpace m) ∈ Ω →
        (fun t : EuclideanSpace ℝ (Fin m) => W (x, t))
          =ᶠ[nhds w] fun t : EuclideanSpace ℝ (Fin m) => u (x, t) * φ (x, t) := by
      intro w hw
      filter_upwards [hopenΩ.mem_nhds hw] with t ht
      exact gluedProd_of_mem ht
    have hev0 : ∀ w : EuclideanSpace ℝ (Fin m), ((x, w) : CapSpace m) ∉ Ω →
        (fun t : EuclideanSpace ℝ (Fin m) => W (x, t))
          =ᶠ[nhds w] fun _ : EuclideanSpace ℝ (Fin m) => (0 : ℝ) := by
      intro w hw
      have hpt : ((x, w) : CapSpace m) ∉ tsupport φ := fun h => hw (hφs h)
      have hopen : IsOpen {t : EuclideanSpace ℝ (Fin m) | ((x, t) : CapSpace m) ∉ tsupport φ} :=
        (isOpen_compl_iff.2 (isClosed_tsupport φ)).preimage hemb
      filter_upwards [hopen.mem_nhds hpt] with t ht
      exact gluedProd_of_notMem_tsupport ht
    have hCD : ContDiff ℝ 1 fun w : EuclideanSpace ℝ (Fin m) => W (x, w) := by
      rw [contDiff_iff_contDiffAt]
      intro w
      by_cases hmem : ((x, w) : CapSpace m) ∈ Ω
      · have hmem' : ((x, w) : CapSpace m) ∈ Ω \ {p : CapSpace m | p.1 ∈ S} :=
          ⟨hmem, by simpa using hxS⟩
        refine ContDiffAt.congr_of_eventuallyEq ?_ (hev w hmem)
        exact (huslice.contDiffAt (hopenΩ'.mem_nhds hmem')).mul hφslice.contDiffAt
      · exact contDiffAt_const.congr_of_eventuallyEq (hev0 w hmem)
    -- the transverse derivative of the glued slice is the integrand
    have hderiv : ∀ w : EuclideanSpace ℝ (Fin m),
        fderiv ℝ (fun t : EuclideanSpace ℝ (Fin m) => W (x, t)) w (EuclideanSpace.single i 1)
          = F (x, w) := by
      intro w
      by_cases hmem : ((x, w) : CapSpace m) ∈ Ω
      · have hmem' : ((x, w) : CapSpace m) ∈ Ω \ {p : CapSpace m | p.1 ∈ S} :=
          ⟨hmem, by simpa using hxS⟩
        have hdiff : DifferentiableAt ℝ u ((x, w) : CapSpace m) :=
          (hu'.contDiffAt (hΩ'.mem_nhds hmem')).differentiableAt le_rfl
        have hU := fderiv_transverseSlice_apply hdiff (x := x) (w := w)
        have hΦ := fderiv_transverseSlice_apply
          (hφ.differentiable le_rfl ((x, w) : CapSpace m)) (x := x) (w := w)
        have hW := (hU.mul hΦ).congr_of_eventuallyEq (hev w hmem)
        rw [hW.fderiv]
        have hg1 : g ((x, w) : CapSpace m) = fderiv ℝ u (x, w) v := by
          rw [hgin _ hmem', hvdef]; rfl
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
          ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.inr_apply,
          hFdef, hg1, hvdef]
        ring
      · have hpt : ((x, w) : CapSpace m) ∉ tsupport φ := fun h => hmem (hφs h)
        have hW : HasFDerivAt (fun t : EuclideanSpace ℝ (Fin m) => W (x, t)) 0 w :=
          (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) w).congr_of_eventuallyEq (hev0 w hmem)
        have h1 : fderiv ℝ φ ((x, w) : CapSpace m) = 0 :=
          Function.notMem_support.1 fun h => hpt (support_fderiv_subset ℝ h)
        have h2 : g ((x, w) : CapSpace m) = 0 := hgout _ hmem
        rw [hW.fderiv]
        simp only [hFdef, h1, h2]
        simp
    have h0 := RobinCaps.Sobolev.Weak.integral_fderiv_single_eq_zero
      (fun w : EuclideanSpace ℝ (Fin m) => W (x, w)) hCD
      (hasCompactSupport_transverseSlice hWcs x) i
    rw [← h0]
    exact integral_congr_ae (.of_forall fun w => (hderiv w).symm)
  -- the interfaces form a null set of axial coordinates
  have hae : (fun x : ℝ => ∫ z : EuclideanSpace ℝ (Fin m), F (x, z))
      =ᵐ[volume] fun _ : ℝ => (0 : ℝ) := by
    have hnull : (volume : Measure ℝ) (S : Set ℝ) = 0 := S.finite_toSet.measure_zero _
    refine ae_iff.2 (measure_mono_null (fun x hx => ?_) hnull)
    simp only [mem_setOf_eq] at hx
    by_contra hxS
    exact hx (hmain x (by simpa using hxS))
  have hIF' : Integrable F
      ((volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin m)))) := by
    rwa [← Measure.volume_eq_prod]
  calc (∫ p, F p)
      = ∫ p, F p ∂((volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin m)))) := by
        rw [← Measure.volume_eq_prod]
    _ = ∫ x, ∫ z, F (x, z) := by rw [integral_prod _ hIF']
    _ = 0 := by rw [integral_congr_ae hae]; simp

/-! ### The main sufficient condition -/

/-- **A continuous, piecewise `C¹` function has its piecewise classical gradient as a weak
gradient.**

`Ω` is open, `S : Finset ℝ` is the (finite) set of interface abscissae, and the interfaces are
the axial hyperplanes `{x = c}`, `c ∈ S`.  If `u` is continuous on `Ω`, is `C¹` on the punctured
domain `Ω' = Ω \ {p | p.1 ∈ S}`, and its classical derivatives are bounded on `Ω'`, then
`(∂ₓu, ∇_z u)` — whose values on the null set of interfaces are irrelevant — is a weak gradient
of `u` on `Ω`.

This covers the manuscript's trial functions of `eq:trial-extension`: `F(x)ψ_R(z)` on the bulk
cylinder glued to the cap pieces across the interface slices. -/
theorem hasWeakGradP_of_piecewise (Ω : Set (CapSpace m)) (hΩ : IsOpen Ω) (S : Finset ℝ)
    (u : CapSpace m → ℝ) (hu : ContinuousOn u Ω)
    (hu' : ContDiffOn ℝ 1 u (Ω \ {p : CapSpace m | p.1 ∈ S}))
    (hbdd : ∃ M : ℝ, ∀ p ∈ Ω \ {p : CapSpace m | p.1 ∈ S},
      |dxP u p| ≤ M ∧ ‖gradZP u p‖ ≤ M) :
    HasWeakGradP Ω u (dxP u) (gradZP u) := by
  obtain ⟨M, hM⟩ := hbdd
  have hΩ' : IsOpen (Ω \ {p : CapSpace m | p.1 ∈ S}) := hΩ.sdiff (isClosed_interfaces S)
  have hΩ'meas : MeasurableSet (Ω \ {p : CapSpace m | p.1 ∈ S}) := hΩ'.measurableSet
  set M₀ : ℝ := max M 0 with hM₀def
  have hM₀ : (0 : ℝ) ≤ M₀ := le_max_right _ _
  have hMM₀ : M ≤ M₀ := le_max_left _ _
  intro φ hφ hφc hφs
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  -- the bounded measurable stand-ins for the classical derivatives
  have hnullS : volume {p : CapSpace m | p.1 ∈ S} = 0 := volume_interfaces_eq_zero S
  refine ⟨?_, fun i => ?_⟩
  · -- axial direction
    set g : CapSpace m → ℝ := (Ω \ {p : CapSpace m | p.1 ∈ S}).indicator (dxP u) with hgdef
    have hgm : Measurable g := (measurable_fderiv_apply_const ℝ u _).indicator hΩ'meas
    have hgb : ∀ p, |g p| ≤ M₀ := by
      intro p
      by_cases hp : p ∈ Ω \ {q : CapSpace m | q.1 ∈ S}
      · rw [hgdef, Set.indicator_of_mem hp]
        exact ((hM p hp).1).trans hMM₀
      · rw [hgdef, Set.indicator_of_notMem hp, abs_zero]; exact hM₀
    have hgin : ∀ p ∈ Ω \ {q : CapSpace m | q.1 ∈ S}, g p = dxP u p :=
      fun p hp => Set.indicator_of_mem hp _
    have hgout : ∀ p, p ∉ Ω → g p = 0 := fun p hp =>
      Set.indicator_of_notMem (fun h => hp h.1) _
    have hzero := integral_axial_piecewise_eq_zero hΩ hu hu' hgm hgb hgin hgout hφ1 hφc hφs
    -- split the integral
    have hPc : Continuous fun p : CapSpace m =>
        u p * fderiv ℝ φ p ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))) :=
      continuous_mul_fderiv_apply hΩ hu hφ1 hφs _
    have hIP : Integrable (fun p : CapSpace m =>
        u p * fderiv ℝ φ p ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m)))) volume :=
      hPc.integrable_of_hasCompactSupport (hasCompactSupport_mul_fderiv_apply hφc _)
    have hIφ : Integrable φ volume := hφ.continuous.integrable_of_hasCompactSupport hφc
    have hIQ : Integrable (fun p : CapSpace m => g p * φ p) volume :=
      hIφ.bdd_mul hgm.aestronglyMeasurable
        (.of_forall fun p => by rw [Real.norm_eq_abs]; exact hgb p)
    rw [integral_add hIP hIQ] at hzero
    -- `g · φ` and `∂ₓu · φ` agree a.e.
    have hQae : (fun p : CapSpace m => g p * φ p)
        =ᵐ[volume] fun p : CapSpace m => dxP u p * φ p := by
      refine ae_iff.2 (measure_mono_null (fun p hp => ?_) hnullS)
      simp only [mem_setOf_eq] at hp
      by_contra hpS
      by_cases hpΩ : p ∈ Ω
      · exact hp (by rw [hgin p ⟨hpΩ, hpS⟩])
      · rw [hgout p hpΩ, image_eq_zero_of_notMem_tsupport fun h => hpΩ (hφs h)] at hp
        exact hp (by ring)
    rw [HasWeakGradP.setIntegral_mul_dirDeriv_eq_integral (u := u) _ hφs,
      HasWeakGradP.setIntegral_mul_eq_integral (g := dxP u) hφs, ← integral_congr_ae hQae]
    linarith
  · -- transverse direction `i`
    set g : CapSpace m → ℝ :=
      (Ω \ {p : CapSpace m | p.1 ∈ S}).indicator (fun p => gradZP u p i) with hgdef
    have hgm : Measurable g := (measurable_fderiv_apply_const ℝ u _).indicator hΩ'meas
    have hgb : ∀ p, |g p| ≤ M₀ := by
      intro p
      by_cases hp : p ∈ Ω \ {q : CapSpace m | q.1 ∈ S}
      · rw [hgdef, Set.indicator_of_mem hp]
        refine le_trans ?_ (((hM p hp).2).trans hMM₀)
        simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (gradZP u p) i
      · rw [hgdef, Set.indicator_of_notMem hp, abs_zero]; exact hM₀
    have hgin : ∀ p ∈ Ω \ {q : CapSpace m | q.1 ∈ S}, g p = gradZP u p i :=
      fun p hp => Set.indicator_of_mem hp _
    have hgout : ∀ p, p ∉ Ω → g p = 0 := fun p hp =>
      Set.indicator_of_notMem (fun h => hp h.1) _
    have hzero :=
      integral_transverse_piecewise_eq_zero hΩ hu hu' hgm hgb i hgin hgout hφ1 hφc hφs
    have hPc : Continuous fun p : CapSpace m =>
        u p * fderiv ℝ φ p ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)) :=
      continuous_mul_fderiv_apply hΩ hu hφ1 hφs _
    have hIP : Integrable (fun p : CapSpace m =>
        u p * fderiv ℝ φ p ((0 : ℝ), EuclideanSpace.single i (1 : ℝ))) volume :=
      hPc.integrable_of_hasCompactSupport (hasCompactSupport_mul_fderiv_apply hφc _)
    have hIφ : Integrable φ volume := hφ.continuous.integrable_of_hasCompactSupport hφc
    have hIQ : Integrable (fun p : CapSpace m => g p * φ p) volume :=
      hIφ.bdd_mul hgm.aestronglyMeasurable
        (.of_forall fun p => by rw [Real.norm_eq_abs]; exact hgb p)
    rw [integral_add hIP hIQ] at hzero
    have hQae : (fun p : CapSpace m => g p * φ p)
        =ᵐ[volume] fun p : CapSpace m => gradZP u p i * φ p := by
      refine ae_iff.2 (measure_mono_null (fun p hp => ?_) hnullS)
      simp only [mem_setOf_eq] at hp
      by_contra hpS
      by_cases hpΩ : p ∈ Ω
      · exact hp (by rw [hgin p ⟨hpΩ, hpS⟩])
      · rw [hgout p hpΩ, image_eq_zero_of_notMem_tsupport fun h => hpΩ (hφs h)] at hp
        exact hp (by ring)
    rw [HasWeakGradP.setIntegral_mul_dirDeriv_eq_integral (u := u) _ hφs,
      HasWeakGradP.setIntegral_mul_eq_integral (g := fun p => gradZP u p i) hφs,
      ← integral_congr_ae hQae]
    linarith

/-! ### The bundled `H¹` element -/

/-- A bounded a.e.-strongly-measurable function on a bounded set is in `L²` of that set. -/
theorem memLp_two_of_bounded_on {F : Type*} [NormedAddCommGroup F] {Ω : Set (CapSpace m)}
    (hΩb : Bornology.IsBounded Ω) {f : CapSpace m → F}
    (hf : AEStronglyMeasurable f (volume.restrict Ω)) (C : ℝ)
    (hb : ∀ᵐ p ∂(volume.restrict Ω), ‖f p‖ ≤ C) : MemLp f 2 (volume.restrict Ω) := by
  haveI : IsFiniteMeasure (volume.restrict Ω) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hΩb.measure_lt_top⟩
  exact MemLp.of_bound hf C hb

/-- The transverse gradient of an arbitrary function is measurable. -/
theorem measurable_gradZP (u : CapSpace m → ℝ) : Measurable (gradZP u) := by
  have hL : Measurable (WithLp.toLp 2 : (Fin m → ℝ) → EuclideanSpace ℝ (Fin m)) :=
    (EuclideanSpace.equiv (Fin m) ℝ).symm.continuous.measurable
  exact hL.comp (measurable_pi_lambda _ fun i => measurable_fderiv_apply_const ℝ u _)

/-- **The bundled `H¹(Ω)` element attached to a continuous, piecewise `C¹` function.**

On a bounded open `Ω`, a bounded function that is continuous on `Ω`, `C¹` off finitely many
axial interface hyperplanes, and has bounded classical derivatives there, is an element of
`H1P Ω` with its piecewise classical derivatives as weak derivatives. -/
def H1P.ofPiecewise (Ω : Set (CapSpace m)) (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (S : Finset ℝ) (u : CapSpace m → ℝ) (hu : ContinuousOn u Ω)
    (hu' : ContDiffOn ℝ 1 u (Ω \ {p : CapSpace m | p.1 ∈ S}))
    (hbdd : ∃ M : ℝ, ∀ p ∈ Ω \ {p : CapSpace m | p.1 ∈ S},
      |dxP u p| ≤ M ∧ ‖gradZP u p‖ ≤ M)
    (hub : ∃ M : ℝ, ∀ p ∈ Ω, |u p| ≤ M) : H1P Ω where
  toFun := u
  gx := dxP u
  gz := gradZP u
  memL2 := by
    obtain ⟨C, hC⟩ := hub
    refine memLp_two_of_bounded_on hΩb (hu.aestronglyMeasurable hΩ.measurableSet) C ?_
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with p hp
    rw [Real.norm_eq_abs]; exact hC p hp
  gx_memL2 := by
    obtain ⟨M, hM⟩ := hbdd
    refine memLp_two_of_bounded_on hΩb
      (measurable_fderiv_apply_const ℝ u _).aestronglyMeasurable M ?_
    filter_upwards [ae_restrict_mem hΩ.measurableSet,
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 (volume_interfaces_eq_zero (m := m) S))]
      with p hp hpS
    rw [Real.norm_eq_abs]; exact (hM p ⟨hp, hpS⟩).1
  gz_memL2 := by
    obtain ⟨M, hM⟩ := hbdd
    refine memLp_two_of_bounded_on hΩb (measurable_gradZP u).aestronglyMeasurable M ?_
    filter_upwards [ae_restrict_mem hΩ.measurableSet,
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 (volume_interfaces_eq_zero (m := m) S))]
      with p hp hpS
    exact (hM p ⟨hp, hpS⟩).2
  hasWeakGrad := hasWeakGradP_of_piecewise Ω hΩ S u hu hu' hbdd

@[simp] theorem H1P.ofPiecewise_toFun (Ω : Set (CapSpace m)) (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (S : Finset ℝ) (u : CapSpace m → ℝ) (hu : ContinuousOn u Ω)
    (hu' : ContDiffOn ℝ 1 u (Ω \ {p : CapSpace m | p.1 ∈ S}))
    (hbdd : ∃ M : ℝ, ∀ p ∈ Ω \ {p : CapSpace m | p.1 ∈ S},
      |dxP u p| ≤ M ∧ ‖gradZP u p‖ ≤ M)
    (hub : ∃ M : ℝ, ∀ p ∈ Ω, |u p| ≤ M) :
    (H1P.ofPiecewise Ω hΩ hΩb S u hu hu' hbdd hub).toFun = u := rfl

@[simp] theorem H1P.ofPiecewise_gx (Ω : Set (CapSpace m)) (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (S : Finset ℝ) (u : CapSpace m → ℝ) (hu : ContinuousOn u Ω)
    (hu' : ContDiffOn ℝ 1 u (Ω \ {p : CapSpace m | p.1 ∈ S}))
    (hbdd : ∃ M : ℝ, ∀ p ∈ Ω \ {p : CapSpace m | p.1 ∈ S},
      |dxP u p| ≤ M ∧ ‖gradZP u p‖ ≤ M)
    (hub : ∃ M : ℝ, ∀ p ∈ Ω, |u p| ≤ M) :
    (H1P.ofPiecewise Ω hΩ hΩb S u hu hu' hbdd hub).gx = dxP u := rfl

@[simp] theorem H1P.ofPiecewise_gz (Ω : Set (CapSpace m)) (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (S : Finset ℝ) (u : CapSpace m → ℝ) (hu : ContinuousOn u Ω)
    (hu' : ContDiffOn ℝ 1 u (Ω \ {p : CapSpace m | p.1 ∈ S}))
    (hbdd : ∃ M : ℝ, ∀ p ∈ Ω \ {p : CapSpace m | p.1 ∈ S},
      |dxP u p| ≤ M ∧ ‖gradZP u p‖ ≤ M)
    (hub : ∃ M : ℝ, ∀ p ∈ Ω, |u p| ≤ M) :
    (H1P.ofPiecewise Ω hΩ hΩb S u hu hu' hbdd hub).gz = gradZP u := rfl

end

end RobinCaps.ThinDomain
