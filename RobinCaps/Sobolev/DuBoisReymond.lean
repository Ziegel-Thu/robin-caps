import RobinCaps.Sobolev.Picone
import RobinCaps.Sobolev.Interval

/-!
# The one-dimensional du Bois-Reymond lemma

This file bridges the *distributional* description of one-dimensional Sobolev functions
(`RobinCaps/Sobolev/Weak.lean`: a function together with a weak derivative tested against
smooth compactly supported functions) and the *concrete* absolutely continuous model
(`RobinCaps/Sobolev/Interval.lean`: `RobinCaps.Sobolev.H1`, an absolutely continuous function
carrying an FTC reconstruction field).

The main results are

* `RobinCaps.Sobolev.HasWeakDeriv`, the one-dimensional weak derivative on an interval
  `(a,b) ⊆ ℝ`;
* `RobinCaps.Sobolev.ae_eq_zero_of_integral_mul_test_eq_zero`, the *fundamental lemma of the
  calculus of variations* in the shape used here (a thin wrapper around mathlib's
  `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`);
* `RobinCaps.Sobolev.ae_const_of_hasWeakDeriv_zero`: a function with vanishing weak derivative
  on `(a,b)` is a.e. constant there (**du Bois-Reymond**);
* `RobinCaps.Sobolev.ae_eq_const_add_integral`: a function with weak derivative `g` agrees
  a.e. on `(a,b)` with `c + ∫ g`, i.e. it has an absolutely continuous representative;
* `RobinCaps.Sobolev.absolutelyContinuousOnInterval_primitive`: the primitive of an `L¹`
  function is absolutely continuous (the `ε`-`δ` absolute continuity of the integral, which
  mathlib `v4.26.0` only provides in its `ℝ≥0∞` form);
* `RobinCaps.Sobolev.primitiveH1` and `RobinCaps.Sobolev.exists_h1_of_hasWeakDeriv`: the
  bridge to the concrete model, producing an element of `RobinCaps.Sobolev.H1 ℓ` that
  represents `u` and whose classical derivative is `g` a.e.

Everything is proved without `sorry`, `axiom` or `admit`.
-/

open MeasureTheory Set Filter

open scoped ContDiff ENNReal Topology Interval

namespace RobinCaps.Sobolev

noncomputable section

/-! ## The one-dimensional weak derivative -/

/-- **Weak derivative on an interval.**  `g` is a weak derivative of `u` on `(a,b)` if
`∫ u φ' = - ∫ g φ` for every smooth function `φ` compactly supported inside `(a,b)`. -/
def HasWeakDeriv (a b : ℝ) (u g : ℝ → ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo a b →
    ∫ x in Ioo a b, u x * deriv φ x = - ∫ x in Ioo a b, g x * φ x

/-! ## Item 1: the fundamental lemma of the calculus of variations in 1-D -/

variable {a b : ℝ}

/-- A test function supported in `(a,b)` only sees `(a,b)`. -/
theorem integral_eq_setIntegral_of_tsupport {f φ : ℝ → ℝ} (hsupp : tsupport φ ⊆ Ioo a b) :
    ∫ x, φ x • f x = ∫ x in Ioo a b, φ x • f x := by
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
  intro x hx
  have hφ : φ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hc => hx (hsupp hc))
  simp [hφ]

/-- **Fundamental lemma of the calculus of variations (1-D).**  If `f` is integrable on the
open interval `(a,b)` and `∫ f φ = 0` for every smooth `φ` compactly supported in `(a,b)`,
then `f = 0` a.e. on `(a,b)`. -/
theorem ae_eq_zero_of_integral_mul_test_eq_zero {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioo a b))
    (h : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo a b →
      ∫ x in Ioo a b, f x * φ x = 0) :
    f =ᵐ[volume.restrict (Ioo a b)] 0 := by
  have key : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ioo a b → f x = 0 := by
    refine (isOpen_Ioo (a := a) (b := b)).ae_eq_zero_of_integral_contDiff_smul_eq_zero
      hf.locallyIntegrableOn ?_
    intro φ hφ hφc hsupp
    rw [integral_eq_setIntegral_of_tsupport (f := f) hsupp]
    have hfun : (fun x => φ x • f x) = fun x => f x * φ x := by
      funext x; simp [mul_comm]
    rw [hfun]
    exact h φ hφ hφc hsupp
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [key] with x hx using hx

/-! ## A normalized bump function supported in `(a,b)` -/

/-- The data of a `ContDiffBump` centred at the midpoint of `(a,b)`, with outer radius
`(b-a)/3`, so that its closed support sits strictly inside `(a,b)`. -/
def midBump (hab : a < b) : ContDiffBump ((a + b) / 2) where
  rIn := (b - a) / 4
  rOut := (b - a) / 3
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

/-- A smooth, nonnegative bump supported in `(a,b)` whose integral is `1`. -/
def bump (hab : a < b) : ℝ → ℝ := (midBump hab).normed volume

theorem bump_contDiff (hab : a < b) : ContDiff ℝ ∞ (bump hab) :=
  (midBump hab).contDiff_normed (n := (⊤ : ℕ∞))

theorem bump_hasCompactSupport (hab : a < b) : HasCompactSupport (bump hab) :=
  (midBump hab).hasCompactSupport_normed

theorem bump_tsupport (hab : a < b) : tsupport (bump hab) ⊆ Ioo a b := by
  have h : tsupport (bump hab) = Metric.closedBall ((a + b) / 2) ((b - a) / 3) :=
    (midBump hab).tsupport_normed_eq
  rw [h, Real.closedBall_eq_Icc]
  intro x hx
  simp only [mem_Icc] at hx
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem bump_integral (hab : a < b) : ∫ x, bump hab x = 1 :=
  (midBump hab).integral_normed

/-! ## Primitives of test functions with vanishing integral -/

/-- **The primitive of a test function with vanishing integral is again a test function.**
If `ψ` is smooth, compactly supported in `(a,b)` and `∫ ψ = 0`, then `x ↦ ∫_a^x ψ` is smooth,
compactly supported in `(a,b)`, and its derivative is `ψ`. -/
theorem exists_test_primitive (hab : a < b) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (hsupp : tsupport ψ ⊆ Ioo a b) (hint : ∫ x, ψ x = 0) :
    ∃ Φ : ℝ → ℝ, ContDiff ℝ ∞ Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ Ioo a b ∧ deriv Φ = ψ := by
  classical
  have hcont : Continuous ψ := hψ.continuous
  set Φ : ℝ → ℝ := fun x => ∫ t in a..x, ψ t with hΦdef
  -- `Φ` is differentiable with derivative `ψ` everywhere.
  have hderiv : ∀ x : ℝ, HasDerivAt Φ (ψ x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable a x)
      (hcont.stronglyMeasurableAtFilter volume (𝓝 x)) hcont.continuousAt
  have hderivEq : deriv Φ = ψ := funext fun x => (hderiv x).deriv
  have hΦsmooth : ContDiff ℝ ∞ Φ :=
    contDiff_infty_iff_deriv.2 ⟨fun x => (hderiv x).differentiableAt, by rw [hderivEq]; exact hψ⟩
  -- A compact, nonempty set containing the support of `ψ` and contained in `(a,b)`.
  set K : Set ℝ := tsupport ψ ∪ {(a + b) / 2} with hKdef
  have hKcompact : IsCompact K := hψc.union isCompact_singleton
  have hmid : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hKsub : K ⊆ Ioo a b := by
    rintro x (hx | hx)
    · exact hsupp hx
    · rw [mem_singleton_iff] at hx; rw [hx]; exact hmid
  have hKne : K.Nonempty := ⟨(a + b) / 2, Or.inr rfl⟩
  set α : ℝ := sInf K with hαdef
  set β : ℝ := sSup K with hβdef
  have hαK : α ∈ K := hKcompact.sInf_mem hKne
  have hβK : β ∈ K := hKcompact.sSup_mem hKne
  have hαa : a < α := (hKsub hαK).1
  have hβb : β < b := (hKsub hβK).2
  have hKIcc : K ⊆ Icc α β := fun x hx =>
    ⟨csInf_le hKcompact.bddBelow hx, le_csSup hKcompact.bddAbove hx⟩
  have hzero : ∀ t : ℝ, t ∉ K → ψ t = 0 := fun t ht =>
    image_eq_zero_of_notMem_tsupport fun hc => ht (Or.inl hc)
  -- `Φ` vanishes to the left of `α`.
  have hleft : ∀ x : ℝ, x < α → Φ x = 0 := by
    intro x hx
    have : EqOn ψ 0 (uIcc a x) := by
      intro t ht
      refine hzero t fun htK => ?_
      have h1 : α ≤ t := (hKIcc htK).1
      have h2 : t ≤ max a x := ht.2
      have h3 : max a x < α := max_lt hαa hx
      linarith
    simp [hΦdef, intervalIntegral.integral_congr this]
  -- `Φ` vanishes to the right of `β`.
  have hright : ∀ x : ℝ, β < x → Φ x = 0 := by
    intro x hx
    have hax : a ≤ x := le_of_lt (lt_trans (lt_of_lt_of_le hαa (hKIcc hαK).2) hx)
    have hsub : ∀ t : ℝ, t ∉ Ioc a x → ψ t = 0 := by
      intro t ht
      refine hzero t fun htK => ?_
      exact ht ⟨(hKsub htK).1, le_trans (hKIcc htK).2 hx.le⟩
    rw [hΦdef]
    simp only
    rw [intervalIntegral.integral_of_le hax,
      setIntegral_eq_integral_of_forall_compl_eq_zero hsub, hint]
  have houtside : ∀ x : ℝ, x ∉ Icc α β → Φ x = 0 := by
    intro x hx
    rw [mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hx | hx
    · exact hleft x hx
    · exact hright x hx
  have hsuppΦ : Function.support Φ ⊆ Icc α β := fun x hx => by
    by_contra hc
    exact hx (houtside x hc)
  have htsuppΦ : tsupport Φ ⊆ Icc α β :=
    closure_minimal hsuppΦ isClosed_Icc
  refine ⟨Φ, hΦsmooth, HasCompactSupport.intro isCompact_Icc houtside, ?_, hderivEq⟩
  refine htsuppΦ.trans fun x hx => ?_
  exact ⟨lt_of_lt_of_le hαa hx.1, lt_of_le_of_lt hx.2 hβb⟩

/-! ## Integrability helpers -/

/-- An integrable function times a continuous compactly supported function is integrable. -/
theorem integrableOn_mul_test {f φ : ℝ → ℝ} (hf : IntegrableOn f (Ioo a b))
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    IntegrableOn (fun x => f x * φ x) (Ioo a b) := by
  obtain ⟨C, hC⟩ := hφc.exists_bound_of_continuous hφ
  exact hf.mul_bdd hφ.aestronglyMeasurable.restrict
    (Filter.Eventually.of_forall fun x => hC x)

/-- The integral of a test function over `(a,b)` is its integral over `ℝ`. -/
theorem setIntegral_test_eq_integral {φ : ℝ → ℝ} (hsupp : tsupport φ ⊆ Ioo a b) :
    ∫ x in Ioo a b, φ x = ∫ x, φ x :=
  setIntegral_eq_integral_of_forall_compl_eq_zero fun _ hx =>
    image_eq_zero_of_notMem_tsupport fun hc => hx (hsupp hc)

/-! ## Item 2: vanishing weak derivative forces a constant -/

/-- **du Bois-Reymond.**  A locally integrable function whose weak derivative on `(a,b)`
vanishes is almost everywhere constant on `(a,b)`. -/
theorem ae_const_of_hasWeakDeriv_zero (hab : a < b) {u : ℝ → ℝ}
    (hu : IntegrableOn u (Ioo a b)) (h : HasWeakDeriv a b u 0) :
    ∃ c : ℝ, u =ᵐ[volume.restrict (Ioo a b)] fun _ => c := by
  classical
  set ρ : ℝ → ℝ := bump hab with hρdef
  have hρsmooth : ContDiff ℝ ∞ ρ := bump_contDiff hab
  have hρcont : Continuous ρ := hρsmooth.continuous
  have hρc : HasCompactSupport ρ := bump_hasCompactSupport hab
  have hρsupp : tsupport ρ ⊆ Ioo a b := bump_tsupport hab
  have hρint : ∫ x, ρ x = 1 := bump_integral hab
  set c : ℝ := ∫ x in Ioo a b, u x * ρ x with hcdef
  refine ⟨c, ?_⟩
  -- The key identity `∫ (u - c) φ = 0` for every test function `φ`.
  have key : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo a b →
      ∫ x in Ioo a b, (u x - c) * φ x = 0 := by
    intro φ hφ hφc hφsupp
    have hφcont : Continuous φ := hφ.continuous
    set I : ℝ := ∫ x, φ x with hIdef
    set ψ : ℝ → ℝ := fun x => φ x - I * ρ x with hψdef
    have hψsmooth : ContDiff ℝ ∞ ψ := hφ.sub (contDiff_const.mul hρsmooth)
    have hψcont : Continuous ψ := hψsmooth.continuous
    have hψzero : ∀ x : ℝ, x ∉ tsupport φ ∪ tsupport ρ → ψ x = 0 := by
      intro x hx
      have h1 : φ x = 0 := image_eq_zero_of_notMem_tsupport fun hc => hx (Or.inl hc)
      have h2 : ρ x = 0 := image_eq_zero_of_notMem_tsupport fun hc => hx (Or.inr hc)
      simp [hψdef, h1, h2]
    have hψc : HasCompactSupport ψ :=
      HasCompactSupport.intro (hφc.union hρc) hψzero
    have hψsupp : tsupport ψ ⊆ Ioo a b := by
      have hcl : tsupport ψ ⊆ tsupport φ ∪ tsupport ρ := by
        refine closure_minimal (fun x hx => ?_) (isClosed_closure.union isClosed_closure)
        by_contra hcon
        exact hx (hψzero x hcon)
      exact hcl.trans (union_subset hφsupp hρsupp)
    have hψint : ∫ x, ψ x = 0 := by
      have h1 : Integrable φ := hφcont.integrable_of_hasCompactSupport hφc
      have h2 : Integrable (fun x => I * ρ x) :=
        (continuous_const.mul hρcont).integrable_of_hasCompactSupport hρc.mul_left
      rw [hψdef]
      rw [integral_sub h1 h2, integral_const_mul, hρint, ← hIdef]
      ring
    obtain ⟨Φ, hΦsmooth, hΦc, hΦsupp, hΦderiv⟩ :=
      exists_test_primitive hab hψsmooth hψc hψsupp hψint
    -- Testing the weak-derivative relation against `Φ` gives `∫ u ψ = 0`.
    have hkey : ∫ x in Ioo a b, u x * ψ x = 0 := by
      have := h Φ hΦsmooth hΦc hΦsupp
      rw [hΦderiv] at this
      simpa using this
    -- Expand `ψ` and rearrange.
    have hsplit : ∫ x in Ioo a b, u x * ψ x
        = (∫ x in Ioo a b, u x * φ x) - I * ∫ x in Ioo a b, u x * ρ x := by
      have h1 : IntegrableOn (fun x => u x * φ x) (Ioo a b) :=
        integrableOn_mul_test hu hφcont hφc
      have h2 : IntegrableOn (fun x => I * (u x * ρ x)) (Ioo a b) :=
        (integrableOn_mul_test hu hρcont hρc).const_mul I
      have hfun : (fun x => u x * ψ x)
          = fun x => u x * φ x - I * (u x * ρ x) := by
        funext x; simp [hψdef]; ring
      rw [hfun, integral_sub h1 h2, integral_const_mul]
    have huφ : ∫ x in Ioo a b, u x * φ x = I * c := by
      rw [hsplit] at hkey
      rw [← hcdef] at hkey
      linarith
    have hcφ : ∫ x in Ioo a b, c * φ x = c * I := by
      rw [integral_const_mul, setIntegral_test_eq_integral hφsupp, ← hIdef]
    have hfun2 : (fun x => (u x - c) * φ x)
        = fun x => u x * φ x - c * φ x := by
      funext x; ring
    have h1 : IntegrableOn (fun x => u x * φ x) (Ioo a b) :=
      integrableOn_mul_test hu hφcont hφc
    have h2 : IntegrableOn (fun x => c * φ x) (Ioo a b) := by
      have : IntegrableOn φ (Ioo a b) :=
        (hφcont.integrable_of_hasCompactSupport hφc).integrableOn
      exact this.const_mul c
    rw [hfun2, integral_sub h1 h2, huφ, hcφ, mul_comm]
    ring
  have hsub : IntegrableOn (fun x => u x - c) (Ioo a b) :=
    hu.sub (integrableOn_const (C := c) (by simp))
  have := ae_eq_zero_of_integral_mul_test_eq_zero hsub key
  filter_upwards [this] with x hx
  have : u x - c = 0 := hx
  linarith

/-! ## Item 3: the primitive of an `L¹` function has that function as weak derivative -/

/-- An interval integral over `a..b` is the set integral over the open interval. -/
theorem intervalIntegral_eq_setIntegral_Ioo {f : ℝ → ℝ} (hab : a ≤ b) :
    ∫ x in a..b, f x = ∫ x in Ioo a b, f x := by
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]

/-- **The primitive of an integrable function has that function as weak derivative.**
This is proved by Fubini on the triangle (`RobinCaps.Sobolev.Picone.integral_primitive_mul`)
and needs no differentiability of the primitive. -/
theorem hasWeakDeriv_primitive (hab : a < b) {g : ℝ → ℝ} (hg : IntegrableOn g (Ioo a b))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Icc a b) :
    HasWeakDeriv a b (fun x => ∫ t in x₀..x, g t) g := by
  have hgI : IntervalIntegrable g volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 hg
  have hmem : ∀ y ∈ Icc a b, y ∈ uIcc a b := by
    rw [uIcc_of_le hab.le]; exact fun _ hy => hy
  have hII : ∀ y z, y ∈ Icc a b → z ∈ Icc a b → IntervalIntegrable g volume y z :=
    fun y z hy hz => hgI.mono_set (uIcc_subset_uIcc (hmem y hy) (hmem z hz))
  intro φ hφ hφc hφsupp
  have hφdiff : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hφ'smooth : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.1 hφ).2
  have hφ'cont : Continuous (deriv φ) := hφ'smooth.continuous
  have hdI : IntervalIntegrable (deriv φ) volume a b := hφ'cont.intervalIntegrable a b
  have hφb : φ b = 0 :=
    image_eq_zero_of_notMem_tsupport fun hc => absurd (hφsupp hc).2 (lt_irrefl b)
  have hφa : φ a = 0 :=
    image_eq_zero_of_notMem_tsupport fun hc => absurd (hφsupp hc).1 (lt_irrefl a)
  -- Fubini on the triangle.
  have hF := Picone.integral_primitive_mul hab.le g (deriv φ) hgI hdI
  -- The inner integral of `φ'` telescopes.
  have hfund : ∀ t : ℝ, ∫ x in t..b, deriv φ x = -φ t := by
    intro t
    rw [intervalIntegral.integral_deriv_eq_sub (fun x _ => hφdiff x)
      (hφ'cont.intervalIntegrable t b), hφb]
    ring
  have hRHS : (∫ t in a..b, g t * ∫ x in t..b, deriv φ x) = -∫ t in a..b, g t * φ t := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [hfund t]
    ring
  -- Split the outer primitive at the base point `x₀`.
  set C : ℝ := ∫ t in a..x₀, g t with hCdef
  set v : ℝ → ℝ := fun x => ∫ t in x₀..x, g t with hvdef
  have hvcont : ContinuousOn v (uIcc a b) :=
    intervalIntegral.continuousOn_primitive_interval' hgI (hmem x₀ hx₀)
  have hvI : IntervalIntegrable (fun x => v x * deriv φ x) volume a b :=
    (hvcont.mul hφ'cont.continuousOn).intervalIntegrable
  have heqOn : EqOn (fun x => (∫ t in a..x, g t) * deriv φ x)
      (fun x => C * deriv φ x + v x * deriv φ x) (uIcc a b) := by
    intro x hx
    rw [uIcc_of_le hab.le] at hx
    have hsplit : (∫ t in a..x, g t) = C + v x :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hII a x₀ ⟨le_rfl, hab.le⟩ hx₀) (hII x₀ x hx₀ hx)).symm
    simp only [hsplit, hvdef, hCdef]
    ring
  rw [intervalIntegral.integral_congr heqOn,
    intervalIntegral.integral_add (hdI.const_mul C) hvI,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_deriv_eq_sub (fun x _ => hφdiff x) hdI,
    hφa, hφb, hRHS] at hF
  simp only [sub_self, mul_zero, zero_add] at hF
  rw [← intervalIntegral_eq_setIntegral_Ioo (f := fun x => (fun x => ∫ t in x₀..x, g t) x * deriv φ x) hab.le,
    ← intervalIntegral_eq_setIntegral_Ioo (f := fun x => g x * φ x) hab.le]
  exact hF

/-- **Main theorem (du Bois-Reymond / ACL in one dimension).**  A function `u` with an `L¹`
weak derivative `g` on `(a,b)` agrees almost everywhere on `(a,b)` with a constant plus the
primitive of `g`. -/
theorem ae_eq_const_add_integral (hab : a < b) {u g : ℝ → ℝ}
    (hu : IntegrableOn u (Ioo a b)) (hg : IntegrableOn g (Ioo a b))
    (h : HasWeakDeriv a b u g) :
    ∃ c : ℝ, u =ᵐ[volume.restrict (Ioo a b)]
      fun x => c + ∫ t in ((a + b) / 2)..x, g t := by
  have hmid : ((a + b) / 2) ∈ Icc a b := ⟨by linarith, by linarith⟩
  set v : ℝ → ℝ := fun x => ∫ t in ((a + b) / 2)..x, g t with hvdef
  have hvweak : HasWeakDeriv a b v g := hasWeakDeriv_primitive hab hg hmid
  have hgI : IntervalIntegrable g volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 hg
  have hvcont : ContinuousOn v (uIcc a b) :=
    intervalIntegral.continuousOn_primitive_interval' hgI (by rw [uIcc_of_le hab.le]; exact hmid)
  have hvIcc : ContinuousOn v (Icc a b) := by rwa [uIcc_of_le hab.le] at hvcont
  have hvint : IntegrableOn v (Ioo a b) :=
    (hvIcc.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  -- `u - v` has vanishing weak derivative.
  have hsub : HasWeakDeriv a b (fun x => u x - v x) 0 := by
    intro φ hφ hφc hφsupp
    have hφcont : Continuous φ := hφ.continuous
    have hφ'cont : Continuous (deriv φ) := ((contDiff_infty_iff_deriv.1 hφ).2).continuous
    have hφ'c : HasCompactSupport (deriv φ) := hφc.deriv
    have h1 : IntegrableOn (fun x => u x * deriv φ x) (Ioo a b) :=
      integrableOn_mul_test hu hφ'cont hφ'c
    have h2 : IntegrableOn (fun x => v x * deriv φ x) (Ioo a b) :=
      integrableOn_mul_test hvint hφ'cont hφ'c
    have hfun : (fun x => (u x - v x) * deriv φ x)
        = fun x => u x * deriv φ x - v x * deriv φ x := by
      funext x; ring
    rw [hfun, integral_sub h1 h2, h φ hφ hφc hφsupp, hvweak φ hφ hφc hφsupp]
    simp
  obtain ⟨c, hc⟩ := ae_const_of_hasWeakDeriv_zero hab (hu.sub hvint) hsub
  refine ⟨c, ?_⟩
  filter_upwards [hc] with x hx
  have hx' : u x - v x = c := hx
  show u x = c + v x
  linarith

/-! ## Item 4: absolute continuity of the primitive -/

/-- **The primitive of an integrable function is absolutely continuous.**  This is the
`ε`-`δ` form of the absolute continuity of the Lebesgue integral; mathlib `v4.26.0` has the
`ℝ≥0∞` statement (`MeasureTheory.exists_pos_setLIntegral_lt_of_measure_lt`) but not this
consequence. -/
theorem absolutelyContinuousOnInterval_primitive {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℝ}
    (hg : IntegrableOn g (Ioc a b)) {x₀ : ℝ} (hx₀ : x₀ ∈ Icc a b) :
    AbsolutelyContinuousOnInterval (fun x => ∫ t in x₀..x, g t) a b := by
  classical
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hgI : IntervalIntegrable g volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hg
  have hII : ∀ y z, y ∈ Icc a b → z ∈ Icc a b → IntervalIntegrable g volume y z := by
    intro y z hy hz
    exact hgI.mono_set (uIcc_subset_uIcc (by rw [huIcc]; exact hy) (by rw [huIcc]; exact hz))
  set G : ℝ → ℝ≥0∞ := fun t => ‖(Ioc a b).indicator g t‖ₑ with hGdef
  have hGfin : ∫⁻ t, G t ≠ (⊤ : ℝ≥0∞) := by
    have h1 : ∫⁻ t, G t = ∫⁻ t in Ioc a b, ‖g t‖ₑ := by
      rw [← lintegral_indicator measurableSet_Ioc]
      refine lintegral_congr fun t => ?_
      by_cases ht : t ∈ Ioc a b
      · rw [Set.indicator_of_mem ht]
        show ‖(Ioc a b).indicator g t‖ₑ = ‖g t‖ₑ
        rw [Set.indicator_of_mem ht]
      · rw [Set.indicator_of_notMem ht]
        show ‖(Ioc a b).indicator g t‖ₑ = 0
        rw [Set.indicator_of_notMem ht, enorm_zero]
    rw [h1]
    exact ne_of_lt hg.hasFiniteIntegral
  rw [absolutelyContinuousOnInterval_iff]
  intro ε hε
  obtain ⟨δ, hδ0, hδ⟩ :=
    exists_pos_setLIntegral_lt_of_measure_lt (μ := volume) hGfin
      (ε := ENNReal.ofReal ε) (by simpa using hε)
  -- Turn the `ℝ≥0∞`-threshold `δ` into a real one.
  have hmin_ne_top : min δ 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have hmin_pos : 0 < min δ 1 := lt_min hδ0 one_pos
  have htoReal_pos : 0 < (min δ 1).toReal := ENNReal.toReal_pos hmin_pos.ne' hmin_ne_top
  refine ⟨(min δ 1).toReal / 2, by linarith, ?_⟩
  rintro ⟨n, e⟩ ⟨hmem, hdisj⟩ hlen
  simp only at hmem hdisj hlen ⊢
  set S : ℕ → Set ℝ := fun i => uIoc (e i).1 (e i).2 with hSdef
  have hmemIcc : ∀ i ∈ Finset.range n, (e i).1 ∈ Icc a b ∧ (e i).2 ∈ Icc a b := by
    intro i hi
    have := hmem i hi
    rwa [huIcc] at this
  have hSsub : ∀ i ∈ Finset.range n, S i ⊆ Ioc a b := by
    intro i hi t ht
    obtain ⟨h1, h2⟩ := hmemIcc i hi
    have hmin : a ≤ min (e i).1 (e i).2 := le_min h1.1 h2.1
    have hmax : max (e i).1 (e i).2 ≤ b := max_le h1.2 h2.2
    have ht' : t ∈ Ioc (min (e i).1 (e i).2) (max (e i).1 (e i).2) := ht
    exact ⟨lt_of_le_of_lt hmin ht'.1, le_trans ht'.2 hmax⟩
  have hSmeas : ∀ i ∈ Finset.range n, MeasurableSet (S i) := fun i _ => measurableSet_uIoc
  have hSvol : ∀ i : ℕ, volume (S i) = ENNReal.ofReal (dist (e i).1 (e i).2) := by
    intro i
    have h1 : S i = Ioc (min (e i).1 (e i).2) (max (e i).1 (e i).2) := rfl
    rw [h1, Real.volume_Ioc, max_sub_min_eq_abs, Real.dist_eq, abs_sub_comm]
  -- The union of the intervals has small measure.
  set U : Set ℝ := ⋃ i ∈ Finset.range n, S i with hUdef
  have hUvol : volume U < δ := by
    have h1 : volume U ≤ ∑ i ∈ Finset.range n, volume (S i) :=
      measure_biUnion_finset_le _ _
    have h2 : ∑ i ∈ Finset.range n, volume (S i)
        = ENNReal.ofReal (∑ i ∈ Finset.range n, dist (e i).1 (e i).2) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => dist_nonneg)]
      exact Finset.sum_congr rfl fun i _ => hSvol i
    have h3 : ENNReal.ofReal (∑ i ∈ Finset.range n, dist (e i).1 (e i).2)
        < ENNReal.ofReal ((min δ 1).toReal) :=
      (ENNReal.ofReal_lt_ofReal_iff htoReal_pos).2 (by linarith)
    rw [ENNReal.ofReal_toReal hmin_ne_top] at h3
    exact lt_of_le_of_lt (h1.trans_eq h2) (lt_of_lt_of_le h3 (min_le_left _ _))
  have hUint : ∫⁻ t in U, G t < ENNReal.ofReal ε := hδ U hUvol
  -- Each increment is controlled by the integral of `‖g‖` over the corresponding interval.
  have hincr : ∀ i ∈ Finset.range n,
      ENNReal.ofReal (dist (∫ t in x₀..(e i).1, g t) (∫ t in x₀..(e i).2, g t))
        ≤ ∫⁻ t in S i, G t := by
    intro i hi
    obtain ⟨h1, h2⟩ := hmemIcc i hi
    have hsub : (∫ t in x₀..(e i).1, g t) - (∫ t in x₀..(e i).2, g t)
        = ∫ t in (e i).2..(e i).1, g t :=
      intervalIntegral.integral_interval_sub_left (hII x₀ (e i).1 hx₀ h1)
        (hII x₀ (e i).2 hx₀ h2)
    rw [Real.dist_eq, hsub, intervalIntegral.abs_integral_eq_abs_integral_uIoc,
      ← Real.enorm_eq_ofReal_abs]
    refine le_trans (enorm_integral_le_lintegral_enorm _) ?_
    have huIoc : Ι (e i).2 (e i).1 = S i := uIoc_comm _ _
    rw [huIoc]
    refine le_of_eq (setLIntegral_congr_fun (hSmeas i hi) fun t ht => ?_)
    show ‖g t‖ₑ = ‖(Ioc a b).indicator g t‖ₑ
    rw [Set.indicator_of_mem (hSsub i hi ht)]
  refine (ENNReal.ofReal_lt_ofReal_iff hε).1 ?_
  calc ENNReal.ofReal (∑ i ∈ Finset.range n,
        dist (∫ t in x₀..(e i).1, g t) (∫ t in x₀..(e i).2, g t))
      = ∑ i ∈ Finset.range n,
          ENNReal.ofReal (dist (∫ t in x₀..(e i).1, g t) (∫ t in x₀..(e i).2, g t)) :=
        ENNReal.ofReal_sum_of_nonneg fun _ _ => dist_nonneg
    _ ≤ ∑ i ∈ Finset.range n, ∫⁻ t in S i, G t := Finset.sum_le_sum hincr
    _ = ∫⁻ t in U, G t := (lintegral_biUnion_finset hdisj hSmeas G).symm
    _ < ENNReal.ofReal ε := hUint

/-! ## Item 4: the concrete absolutely continuous representative -/

/-- **Lebesgue differentiation.**  The derivative of `c + ∫_{x₀}^{·} g` is `g` almost
everywhere on `Ι a b`. -/
theorem ae_deriv_primitive {a b : ℝ} {g : ℝ → ℝ} (hgI : IntervalIntegrable g volume a b)
    (c : ℝ) {x₀ : ℝ} (hx₀ : x₀ ∈ uIcc a b) :
    (fun x => deriv (fun y => c + ∫ t in x₀..y, g t) x) =ᵐ[volume.restrict (Ι a b)] g := by
  have hLDT := hgI.ae_hasDerivAt_integral
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [hLDT] with x hx hxmem
  have hxuIcc : x ∈ uIcc a b := uIoc_subset_uIcc hxmem
  exact ((hx hxuIcc x₀ hx₀).const_add c).deriv

/-- **The absolutely continuous representative.**  From an `L¹ ∩ L²`-derivative `g` and a
constant `c`, the primitive `c + ∫₀^· g` is an element of the concrete model `H1 ℓ`. -/
def primitiveH1 {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {g : ℝ → ℝ} (hgI : IntervalIntegrable g volume 0 ℓ)
    (hg2 : IntervalIntegrable (fun x => g x ^ 2) volume 0 ℓ) (c : ℝ) : H1 ℓ where
  toFun := fun x => c + ∫ t in (0 : ℝ)..x, g t
  ac := by
    have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) 0 ℓ :=
      ((LipschitzWith.const c).lipschitzOnWith).absolutelyContinuousOnInterval
    exact hconst.fun_add (absolutelyContinuousOnInterval_primitive hℓ
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hℓ).1 hgI) ⟨le_rfl, hℓ⟩)
  deriv_int := by
    have hae := ae_deriv_primitive hgI c (x₀ := (0 : ℝ)) left_mem_uIcc
    exact hgI.congr_ae hae.symm
  deriv_sq_int := by
    have hae := ae_deriv_primitive hgI c (x₀ := (0 : ℝ)) left_mem_uIcc
    refine hg2.congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
  ftc := by
    intro x hx
    have hae := ae_deriv_primitive hgI c (x₀ := (0 : ℝ)) left_mem_uIcc
    have hsub : Ι (0 : ℝ) x ⊆ Ι (0 : ℝ) ℓ := by
      rw [uIoc_of_le hx.1, uIoc_of_le hℓ]
      exact Ioc_subset_Ioc le_rfl hx.2
    have hae' : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ι (0 : ℝ) x →
        deriv (fun y => c + ∫ s in (0 : ℝ)..y, g s) t = g t := by
      rw [← ae_restrict_iff' measurableSet_uIoc]
      exact hae.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
    rw [intervalIntegral.integral_congr_ae hae']
    simp

theorem primitiveH1_toFun {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {g : ℝ → ℝ} (hgI : IntervalIntegrable g volume 0 ℓ)
    (hg2 : IntervalIntegrable (fun x => g x ^ 2) volume 0 ℓ) (c : ℝ) :
    (primitiveH1 hℓ hgI hg2 c).toFun = fun x => c + ∫ t in (0 : ℝ)..x, g t := rfl

/-- **The bridge between the weak and the concrete model.**  A function `u` with an
`L¹ ∩ L²` weak derivative `g` on `(0,ℓ)` has an absolutely continuous representative in the
concrete Sobolev layer `RobinCaps.Sobolev.H1 ℓ`, whose classical derivative is `g` a.e. -/
theorem exists_h1_of_hasWeakDeriv {ℓ : ℝ} (hℓ : 0 < ℓ) {u g : ℝ → ℝ}
    (hu : IntegrableOn u (Ioo 0 ℓ)) (hg : IntegrableOn g (Ioo 0 ℓ))
    (hg2 : IntegrableOn (fun x => g x ^ 2) (Ioo 0 ℓ)) (h : HasWeakDeriv 0 ℓ u g) :
    ∃ w : H1 ℓ, w.toFun =ᵐ[volume.restrict (Ioo 0 ℓ)] u ∧
      deriv w.toFun =ᵐ[volume.restrict (Ioo 0 ℓ)] g := by
  have hgI : IntervalIntegrable g volume 0 ℓ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hℓ.le).2 hg
  have hg2I : IntervalIntegrable (fun x => g x ^ 2) volume 0 ℓ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hℓ.le).2 hg2
  obtain ⟨c₀, hc₀⟩ := ae_eq_const_add_integral hℓ hu hg h
  set c : ℝ := c₀ - ∫ t in (0 : ℝ)..((0 + ℓ) / 2), g t with hcdef
  refine ⟨primitiveH1 hℓ.le hgI hg2I c, ?_, ?_⟩
  · rw [primitiveH1_toFun]
    have hmid : ((0 + ℓ) / 2) ∈ Icc (0 : ℝ) ℓ := ⟨by linarith, by linarith⟩
    have hmem : ∀ y ∈ Icc (0 : ℝ) ℓ, y ∈ uIcc (0 : ℝ) ℓ := by
      rw [uIcc_of_le hℓ.le]; exact fun _ hy => hy
    have hII : ∀ y z, y ∈ Icc (0 : ℝ) ℓ → z ∈ Icc (0 : ℝ) ℓ →
        IntervalIntegrable g volume y z :=
      fun y z hy hz => hgI.mono_set (uIcc_subset_uIcc (hmem y hy) (hmem z hz))
    filter_upwards [hc₀, ae_restrict_mem measurableSet_Ioo] with x hx hxmem
    have hxIcc : x ∈ Icc (0 : ℝ) ℓ := Ioo_subset_Icc_self hxmem
    have hsplit : (∫ t in (0 : ℝ)..x, g t)
        = (∫ t in (0 : ℝ)..((0 + ℓ) / 2), g t) + ∫ t in ((0 + ℓ) / 2)..x, g t :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hII 0 ((0 + ℓ) / 2) ⟨le_rfl, hℓ.le⟩ hmid) (hII ((0 + ℓ) / 2) x hmid hxIcc)).symm
    rw [hx, hsplit, hcdef]
    ring
  · have hae := ae_deriv_primitive hgI c (x₀ := (0 : ℝ)) left_mem_uIcc
    have hsub : Ioo (0 : ℝ) ℓ ⊆ Ι (0 : ℝ) ℓ := by
      rw [uIoc_of_le hℓ.le]; exact Ioo_subset_Ioc_self
    exact hae.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))

end

end RobinCaps.Sobolev
