import RobinCaps.Sobolev.VariationBridge

set_option linter.style.longLine false

/-!
# U-SOB-3: Picone-type lower bounds for the one-dimensional Robin form

This file proves the analytic content of the *lower* half of the min–max
characterization of the first two interval Robin eigenvalues (manuscript
`reference/robin_endcaps_corrected_en.tex`, `lem:interval`, lines 343–380):

* `picone_one`: `μ₁ · N[u] ≤ a_{p,q;ℓ}[u]` for every `u ∈ H¹(0,ℓ)`;
* `picone_two`: `μ₂ · N[u] ≤ a_{p,q;ℓ}[u]` for every `u ∈ H¹(0,ℓ)` vanishing at the
  interior node `x₁ = (arctan(p/k₂) + π/2)/k₂` of the second eigenfunction.

## Method

Let `f(x) = cos (κ x - θ)` be positive on `[a,b]` and put `w = f'/f`, so that
`w' = -κ² - w²` (Riccati).  For `u ∈ H¹` one has the Picone identity
`0 ≤ ∫ (u' - u w)² = ∫ u'² + u(a)² w(a) - u(b)² w(b) - κ² ∫ u²`, obtained from the
integration-by-parts formula `∫ 2 u u' w = [u² w]ₐᵇ - ∫ u² w'`.

Since an element of `H1 ℓ` is only known to be reconstructed from its derivative
(`H1.ftc`), and is not differentiable everywhere, the integration by parts is proved
via **Fubini on the triangle** `{a < t ≤ x ≤ b}` (`integral_primitive_mul`):
`∫ₐᵇ (∫ₐˣ f) h = ∫ₐᵇ f(t) (∫ₜᵇ h) dt`.  Applied with `f = h = u'` this gives the chain
rule for squares (`sq_sub_sq_eq_integral_of_ftc`); applied with `f = 2 u u'`, `h = w'`
it gives the integration by parts (`ibp_sq_of_ftc`).

For `j = 1` the eigenfunction itself is positive on `[0,ℓ]` and `w(0) = p`, `w(ℓ) = -q`.
For `j = 2` the eigenfunction changes sign at the node `x₁`; instead of a singular
limiting argument we use, for every `k' ∈ (0, k₂)`, the *shifted* test functions
`cos (k' x - arctan (p/k'))` on `[0,x₁]` and `cos (k' (ℓ - x) - arctan (q/k'))` on
`[x₁,ℓ]`, which are positive on the respective closed intervals, have the correct Robin
ratios `p`, `-q` at the outer endpoints, and whose contribution at the node is killed by
`u(x₁) = 0`.  This yields `k'² N[u] ≤ a[u]` for all `k' < k₂`, and `k' → k₂` gives the claim.

Everything below is proved without `sorry`, `axiom` or `admit`.
-/

open MeasureTheory Set Filter
open scoped Topology Interval

namespace RobinCaps.Sobolev.Picone

noncomputable section

/-! ## Fubini on the triangle and integration by parts for `H¹`-type functions -/

/-- Fubini on the triangle `{a < t ≤ x ≤ b}`. -/
theorem integral_primitive_mul {a b : ℝ} (hab : a ≤ b) (f h : ℝ → ℝ)
    (hf : IntervalIntegrable f volume a b) (hh : IntervalIntegrable h volume a b) :
    ∫ x in a..b, (∫ t in a..x, f t) * h x = ∫ t in a..b, f t * ∫ x in t..b, h x := by
  have hfμ : Integrable f (volume.restrict (Ioc a b)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hf
  have hhμ : Integrable h (volume.restrict (Ioc a b)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hh
  let F : ℝ → ℝ → ℝ := fun x t => if t ≤ x then h x * f t else 0
  have hFint : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b))) := by
    have h1 : Integrable (fun z : ℝ × ℝ => h z.1 * f z.2)
        ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b))) := hhμ.mul_prod hfμ
    have h2 := h1.indicator (measurableSet_le measurable_snd measurable_fst)
    refine h2.congr (Eventually.of_forall fun z => ?_)
    simp only [Function.uncurry, F, Set.indicator_apply, Set.mem_setOf_eq]
  have hswap := MeasureTheory.integral_integral_swap hFint
  have hL : (∫ x, ∫ t, F x t ∂(volume.restrict (Ioc a b)) ∂(volume.restrict (Ioc a b)))
      = ∫ x in a..b, (∫ t in a..x, f t) * h x := by
    rw [intervalIntegral.integral_of_le hab]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    have hfun : (fun t => F x t) = (Iic x).indicator (fun t => h x * f t) := by
      funext t
      simp only [F, Set.indicator_apply, Set.mem_Iic]
    simp only [hfun]
    rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
    have hset : Iic x ∩ Ioc a b = Ioc a x := by
      ext t
      simp only [mem_inter_iff, mem_Iic, mem_Ioc]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans hx.2⟩
    rw [hset, integral_const_mul, ← intervalIntegral.integral_of_le hx.1.le]
    ring
  have hR : (∫ t, ∫ x, F x t ∂(volume.restrict (Ioc a b)) ∂(volume.restrict (Ioc a b)))
      = ∫ t in a..b, f t * ∫ x in t..b, h x := by
    rw [intervalIntegral.integral_of_le hab]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    have hfun : (fun x => F x t) = (Ici t).indicator (fun x => h x * f t) := by
      funext x
      simp only [F, Set.indicator_apply, Set.mem_Ici]
    simp only [hfun]
    rw [integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
    have hset : Ici t ∩ Ioc a b = Icc t b := by
      ext x
      simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
      constructor
      · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, lt_of_lt_of_le ht.1 h1, h2⟩
    rw [hset, integral_Icc_eq_integral_Ioc, integral_mul_const,
      ← intervalIntegral.integral_of_le ht.2]
    ring
  rw [← hL, ← hR, hswap]


/-- Continuity of a function reconstructed from an integrable derivative. -/
theorem continuousOn_of_ftc {a b : ℝ} (hab : a ≤ b) (g : ℝ → ℝ)
    (hg : IntervalIntegrable g volume a b) (u : ℝ → ℝ)
    (hu : ∀ x ∈ Icc a b, u x = u a + ∫ t in a..x, g t) :
    ContinuousOn u (Icc a b) := by
  have hprim : ContinuousOn (fun x => ∫ t in a..x, g t) (Icc a b) := by
    have := intervalIntegral.continuousOn_primitive_interval' hg (left_mem_uIcc (a := a) (b := b))
    rwa [uIcc_of_le hab] at this
  exact (continuousOn_const.add hprim).congr hu

/-- Chain rule for squares. -/
theorem sq_sub_sq_eq_integral_of_ftc {a b : ℝ} (hab : a ≤ b) (g : ℝ → ℝ)
    (hg : IntervalIntegrable g volume a b) (u : ℝ → ℝ)
    (hu : ∀ x ∈ Icc a b, u x = u a + ∫ t in a..x, g t) :
    ∀ x ∈ Icc a b, u x ^ 2 - u a ^ 2 = ∫ t in a..x, 2 * u t * g t := by
  intro x hx
  have hgx : IntervalIntegrable g volume a x :=
    hg.mono_set (by rw [uIcc_of_le hx.1, uIcc_of_le hab]; exact Icc_subset_Icc le_rfl hx.2)
  have hGcont : ContinuousOn (fun t => ∫ s in a..t, g s) (Icc a x) := by
    have := intervalIntegral.continuousOn_primitive_interval' hgx (left_mem_uIcc (a := a) (b := x))
    rwa [uIcc_of_le hx.1] at this
  have hGg : IntervalIntegrable (fun t => (∫ s in a..t, g s) * g t) volume a x :=
    hgx.continuousOn_mul (by rw [uIcc_of_le hx.1]; exact hGcont)
  have hF := integral_primitive_mul hx.1 g g hgx hgx
  -- rewrite the right side of Fubini
  have hR : (∫ t in a..x, g t * ∫ s in t..x, g s)
      = (∫ s in a..x, g s) * (∫ s in a..x, g s) - ∫ t in a..x, (∫ s in a..t, g s) * g t := by
    have h1 : ∀ t ∈ uIcc a x, g t * ∫ s in t..x, g s
        = (∫ s in a..x, g s) * g t - (∫ s in a..t, g s) * g t := by
      intro t ht
      rw [uIcc_of_le hx.1] at ht
      have hgt : IntervalIntegrable g volume a t :=
        hgx.mono_set (by rw [uIcc_of_le ht.1, uIcc_of_le hx.1]; exact Icc_subset_Icc le_rfl ht.2)
      rw [← intervalIntegral.integral_interval_sub_left hgx hgt]; ring
    rw [intervalIntegral.integral_congr h1, intervalIntegral.integral_sub
      (hgx.const_mul _) hGg, intervalIntegral.integral_const_mul]
  have hkey : 2 * ∫ t in a..x, (∫ s in a..t, g s) * g t
      = (∫ s in a..x, g s) * (∫ s in a..x, g s) := by
    rw [hR] at hF; linarith [hF]
  have h2 : ∀ t ∈ uIcc a x, 2 * u t * g t = 2 * u a * g t + 2 * ((∫ s in a..t, g s) * g t) := by
    intro t ht
    rw [uIcc_of_le hx.1] at ht
    rw [hu t ⟨ht.1, ht.2.trans hx.2⟩]; ring
  rw [intervalIntegral.integral_congr h2, intervalIntegral.integral_add
    (hgx.const_mul _) (hGg.const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hkey, hu x hx]
  ring

/-- Integration by parts `∫ 2 u g w = [u² w] - ∫ u² w'` for `u = u a + ∫ g`. -/
theorem ibp_sq_of_ftc {a b : ℝ} (hab : a ≤ b) (g : ℝ → ℝ)
    (hg : IntervalIntegrable g volume a b) (u : ℝ → ℝ)
    (hu : ∀ x ∈ Icc a b, u x = u a + ∫ t in a..x, g t) (w w' : ℝ → ℝ)
    (hw : ∀ x ∈ Icc a b, HasDerivAt w (w' x) x) (hw' : ContinuousOn w' (Icc a b)) :
    ∫ x in a..b, 2 * u x * g x * w x
      = u b ^ 2 * w b - u a ^ 2 * w a - ∫ x in a..b, u x ^ 2 * w' x := by
  have hucont : ContinuousOn u (Icc a b) := continuousOn_of_ftc hab g hg u hu
  have hwcont : ContinuousOn w (Icc a b) := fun x hx => (hw x hx).continuousAt.continuousWithinAt
  have hw'int : IntervalIntegrable w' volume a b :=
    (by rw [uIcc_of_le hab]; exact hw' : ContinuousOn w' (uIcc a b)).intervalIntegrable
  have hf : IntervalIntegrable (fun t => 2 * u t * g t) volume a b := by
    have := hg.continuousOn_mul (g := fun t => 2 * u t)
      (by rw [uIcc_of_le hab]; exact continuousOn_const.mul hucont)
    exact this.congr fun t _ => by ring
  have hsq := sq_sub_sq_eq_integral_of_ftc hab g hg u hu
  have hF := integral_primitive_mul hab (fun t => 2 * u t * g t) w' hf hw'int
  -- FTC for w on [t, b]
  have hftc : ∀ t ∈ Icc a b, ∫ x in t..b, w' x = w b - w t := by
    intro t ht
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x hx
      rw [uIcc_of_le ht.2] at hx
      exact hw x ⟨ht.1.trans hx.1, hx.2⟩
    · exact hw'int.mono_set (by rw [uIcc_of_le ht.2, uIcc_of_le hab]; exact Icc_subset_Icc ht.1 le_rfl)
  have hL : (∫ x in a..b, (∫ t in a..x, 2 * u t * g t) * w' x)
      = (∫ x in a..b, u x ^ 2 * w' x) - u a ^ 2 * (w b - w a) := by
    have h1 : ∀ x ∈ uIcc a b, (∫ t in a..x, 2 * u t * g t) * w' x
        = u x ^ 2 * w' x - u a ^ 2 * w' x := by
      intro x hx
      rw [uIcc_of_le hab] at hx
      rw [← hsq x hx]; ring
    have hu2w' : IntervalIntegrable (fun x => u x ^ 2 * w' x) volume a b :=
      (by rw [uIcc_of_le hab]; exact (hucont.pow 2).mul hw' :
        ContinuousOn (fun x => u x ^ 2 * w' x) (uIcc a b)).intervalIntegrable
    rw [intervalIntegral.integral_congr h1, intervalIntegral.integral_sub hu2w'
      (hw'int.const_mul _), intervalIntegral.integral_const_mul,
      hftc a ⟨le_rfl, hab⟩]
  have hR : (∫ t in a..b, 2 * u t * g t * ∫ x in t..b, w' x)
      = w b * (u b ^ 2 - u a ^ 2) - ∫ x in a..b, 2 * u x * g x * w x := by
    have h1 : ∀ t ∈ uIcc a b, 2 * u t * g t * ∫ x in t..b, w' x
        = w b * (2 * u t * g t) - 2 * u t * g t * w t := by
      intro t ht
      rw [uIcc_of_le hab] at ht
      rw [hftc t ht]; ring
    have hfw : IntervalIntegrable (fun t => 2 * u t * g t * w t) volume a b :=
      hf.mul_continuousOn (by rw [uIcc_of_le hab]; exact hwcont)
    rw [intervalIntegral.integral_congr h1, intervalIntegral.integral_sub
      (hf.const_mul _) hfw, intervalIntegral.integral_const_mul, ← hsq b ⟨hab, le_rfl⟩]
  rw [hL, hR] at hF
  linarith [hF]

/-- The generic Picone lower bound. -/
theorem picone_of_ftc {a b : ℝ} (hab : a ≤ b) (g : ℝ → ℝ)
    (hg : IntervalIntegrable g volume a b)
    (hg2 : IntervalIntegrable (fun x => g x ^ 2) volume a b) (u : ℝ → ℝ)
    (hu : ∀ x ∈ Icc a b, u x = u a + ∫ t in a..x, g t) (w w' : ℝ → ℝ)
    (hw : ∀ x ∈ Icc a b, HasDerivAt w (w' x) x) (hw' : ContinuousOn w' (Icc a b))
    (μ : ℝ) (hww : ∀ x ∈ Icc a b, w' x = -μ - w x ^ 2) :
    μ * ∫ x in a..b, u x ^ 2
      ≤ (∫ x in a..b, g x ^ 2) + u a ^ 2 * w a - u b ^ 2 * w b := by
  have hucont : ContinuousOn u (Icc a b) := continuousOn_of_ftc hab g hg u hu
  have hwcont : ContinuousOn w (Icc a b) := fun x hx => (hw x hx).continuousAt.continuousWithinAt
  have hibp := ibp_sq_of_ftc hab g hg u hu w w' hw hw'
  have hu2 : IntervalIntegrable (fun x => u x ^ 2) volume a b :=
    (by rw [uIcc_of_le hab]; exact hucont.pow 2 :
      ContinuousOn (fun x => u x ^ 2) (uIcc a b)).intervalIntegrable
  have hu2w2 : IntervalIntegrable (fun x => u x ^ 2 * w x ^ 2) volume a b :=
    (by rw [uIcc_of_le hab]; exact (hucont.pow 2).mul (hwcont.pow 2) :
      ContinuousOn (fun x => u x ^ 2 * w x ^ 2) (uIcc a b)).intervalIntegrable
  have hugw : IntervalIntegrable (fun x => 2 * u x * g x * w x) volume a b := by
    have := hg.continuousOn_mul (g := fun x => 2 * u x * w x)
      (by rw [uIcc_of_le hab]; exact (continuousOn_const.mul hucont).mul hwcont)
    exact this.congr fun t _ => by ring
  have hw'eq : (∫ x in a..b, u x ^ 2 * w' x)
      = -μ * (∫ x in a..b, u x ^ 2) - ∫ x in a..b, u x ^ 2 * w x ^ 2 := by
    have h1 : ∀ x ∈ uIcc a b, u x ^ 2 * w' x = -μ * u x ^ 2 - u x ^ 2 * w x ^ 2 := by
      intro x hx
      rw [uIcc_of_le hab] at hx
      rw [hww x hx]; ring
    rw [intervalIntegral.integral_congr h1, intervalIntegral.integral_sub
      (hu2.const_mul _) hu2w2, intervalIntegral.integral_const_mul]
  have hnonneg : 0 ≤ ∫ x in a..b, (g x - u x * w x) ^ 2 :=
    intervalIntegral.integral_nonneg hab fun x _ => sq_nonneg _
  have hexp : (∫ x in a..b, (g x - u x * w x) ^ 2)
      = (∫ x in a..b, g x ^ 2) - (∫ x in a..b, 2 * u x * g x * w x)
        + ∫ x in a..b, u x ^ 2 * w x ^ 2 := by
    have h1 : ∀ x ∈ uIcc a b, (g x - u x * w x) ^ 2
        = g x ^ 2 - 2 * u x * g x * w x + u x ^ 2 * w x ^ 2 := by
      intro x _; ring
    rw [intervalIntegral.integral_congr h1, intervalIntegral.integral_add (hg2.sub hugw) hu2w2,
      intervalIntegral.integral_sub hg2 hugw]
  rw [hexp, hibp, hw'eq] at hnonneg
  linarith [hnonneg]


/-- Picone's inequality with the cosine test function `f(x) = cos (κ x - θ)`, assumed positive
on `[a,b]`, and `w = f'/f = -κ tan (κ x - θ)`. -/
theorem picone_cos {a b : ℝ} (hab : a ≤ b) (κ θ : ℝ)
    (hpos : ∀ x ∈ Icc a b, 0 < Real.cos (κ * x - θ)) (g : ℝ → ℝ)
    (hg : IntervalIntegrable g volume a b)
    (hg2 : IntervalIntegrable (fun x => g x ^ 2) volume a b) (u : ℝ → ℝ)
    (hu : ∀ x ∈ Icc a b, u x = u a + ∫ t in a..x, g t) :
    κ ^ 2 * ∫ x in a..b, u x ^ 2
      ≤ (∫ x in a..b, g x ^ 2)
        + u a ^ 2 * (-κ * Real.sin (κ * a - θ) / Real.cos (κ * a - θ))
        - u b ^ 2 * (-κ * Real.sin (κ * b - θ) / Real.cos (κ * b - θ)) := by
  let w : ℝ → ℝ := fun x => -κ * Real.sin (κ * x - θ) / Real.cos (κ * x - θ)
  let w' : ℝ → ℝ := fun x => -(κ ^ 2) - w x ^ 2
  have hlin : ∀ x, HasDerivAt (fun y : ℝ => κ * y - θ) κ x := fun x => by
    simpa using ((hasDerivAt_id x).const_mul κ).sub_const θ
  have hw : ∀ x ∈ Icc a b, HasDerivAt w (w' x) x := by
    intro x hx
    have hc : Real.cos (κ * x - θ) ≠ 0 := (hpos x hx).ne'
    have hs : HasDerivAt (fun y => Real.sin (κ * y - θ)) (Real.cos (κ * x - θ) * κ) x :=
      (Real.hasDerivAt_sin _).comp x (hlin x)
    have hcs : HasDerivAt (fun y => Real.cos (κ * y - θ)) (-Real.sin (κ * x - θ) * κ) x :=
      (Real.hasDerivAt_cos _).comp x (hlin x)
    have hN : HasDerivAt (fun y => -κ * Real.sin (κ * y - θ))
        (-κ * (Real.cos (κ * x - θ) * κ)) x := hs.const_mul (-κ)
    have := hN.div hcs hc
    convert this using 1
    simp only [w', w]
    field_simp
  have hwcont : ContinuousOn w (Icc a b) := fun x hx => (hw x hx).continuousAt.continuousWithinAt
  have hw' : ContinuousOn w' (Icc a b) := continuousOn_const.sub (hwcont.pow 2)
  exact picone_of_ftc hab g hg hg2 u hu w w' hw hw' (κ ^ 2) (fun x _ => rfl)

/-! ## The `H¹` layer: sub-interval versions of the model data -/

variable {ℓ : ℝ}

/-- The derivative is interval integrable on every sub-interval `[a,b] ⊆ [0,ℓ]`. -/
theorem H1.deriv_int_sub (u : H1 ℓ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ ℓ) :
    IntervalIntegrable (fun x => deriv u.toFun x) volume a b :=
  u.deriv_int.mono_set (by
    rw [uIcc_of_le hab, uIcc_of_le (ha.trans (hab.trans hb))]
    exact Icc_subset_Icc ha hb)

/-- The squared derivative is interval integrable on every sub-interval `[a,b] ⊆ [0,ℓ]`. -/
theorem H1.deriv_sq_int_sub (u : H1 ℓ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ ℓ) :
    IntervalIntegrable (fun x => deriv u.toFun x ^ 2) volume a b :=
  u.deriv_sq_int.mono_set (by
    rw [uIcc_of_le hab, uIcc_of_le (ha.trans (hab.trans hb))]
    exact Icc_subset_Icc ha hb)

/-- The reconstruction identity on a sub-interval: `u x = u a + ∫ₐˣ u'` for `x ∈ [a,b]`. -/
theorem H1.ftc_sub (u : H1 ℓ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ ℓ) :
    ∀ x ∈ Icc a b, u.toFun x = u.toFun a + ∫ t in a..x, deriv u.toFun t := by
  intro x hx
  have h0a : IntervalIntegrable (fun t => deriv u.toFun t) volume 0 a :=
    H1.deriv_int_sub u le_rfl ha (hab.trans hb)
  have hax : IntervalIntegrable (fun t => deriv u.toFun t) volume a x :=
    H1.deriv_int_sub u ha hx.1 (hx.2.trans hb)
  have hsum := intervalIntegral.integral_add_adjacent_intervals h0a hax
  have h1 := u.ftc x ⟨ha.trans hx.1, hx.2.trans hb⟩
  have h2 := u.ftc a ⟨ha, hab.trans hb⟩
  linarith

/-- **Chain rule for squares** on `H¹`: `u(x)² - u(0)² = ∫₀ˣ 2 u u'`. -/
theorem H1.sq_sub_sq_eq_integral (u : H1 ℓ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) ℓ) :
    u.toFun x ^ 2 - u.toFun 0 ^ 2 = ∫ t in (0 : ℝ)..x, 2 * u.toFun t * deriv u.toFun t :=
  sq_sub_sq_eq_integral_of_ftc (hx.1.trans hx.2) _ u.deriv_int _ u.ftc x hx

/-- **Integration by parts** on a sub-interval `[a,b] ⊆ [0,ℓ]` against a `C¹` weight `w`:
`∫ₐᵇ 2 u u' w = u(b)² w(b) - u(a)² w(a) - ∫ₐᵇ u² w'`. -/
theorem H1.ibp_sq_on (u : H1 ℓ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ ℓ)
    (w w' : ℝ → ℝ) (hw : ∀ x ∈ Icc a b, HasDerivAt w (w' x) x)
    (hw' : ContinuousOn w' (Icc a b)) :
    ∫ x in a..b, 2 * u.toFun x * deriv u.toFun x * w x
      = u.toFun b ^ 2 * w b - u.toFun a ^ 2 * w a - ∫ x in a..b, u.toFun x ^ 2 * w' x :=
  ibp_sq_of_ftc hab _ (H1.deriv_int_sub u ha hab hb) _ (H1.ftc_sub u ha hab hb) w w' hw hw'

/-- **Integration by parts** on `[0,ℓ]` against a `C¹` weight `w`. -/
theorem H1.ibp_sq (u : H1 ℓ) (hℓ : 0 < ℓ) (w w' : ℝ → ℝ)
    (hw : ∀ x ∈ Icc (0 : ℝ) ℓ, HasDerivAt w (w' x) x)
    (hw' : ContinuousOn w' (Icc (0 : ℝ) ℓ)) :
    ∫ x in (0 : ℝ)..ℓ, 2 * u.toFun x * deriv u.toFun x * w x
      = u.toFun ℓ ^ 2 * w ℓ - u.toFun 0 ^ 2 * w 0 - ∫ x in (0 : ℝ)..ℓ, u.toFun x ^ 2 * w' x :=
  H1.ibp_sq_on u le_rfl hℓ.le le_rfl w w' hw hw'

/-! ## Elementary facts about `arctan` -/

/-- `k · sin (arctan (a/k)) / cos (arctan (a/k)) = a` for `k ≠ 0`. -/
theorem mul_sin_div_cos_arctan (a k : ℝ) (hk : k ≠ 0) :
    k * (Real.sin (Real.arctan (a / k)) / Real.cos (Real.arctan (a / k))) = a := by
  rw [← Real.tan_eq_sin_div_cos, Real.tan_arctan]
  field_simp

/-! ## The first eigenvalue -/

/-- **Picone's inequality for `μ₁`**: `μ₁ · N[u] ≤ a_{p,q;ℓ}[u]` for every `u ∈ H¹(0,ℓ)`. -/
theorem picone_one (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) (u : H1 ℓ) :
    Interval.mu p q ℓ 1 hp hq hℓ (le_refl 1) * mass ℓ u ≤ robinForm p q ℓ u := by
  have hphase := Interval.phaseRoot_eq p q ℓ 1 hp hq hℓ (le_refl 1)
  simp only [Interval.phaseFun, Nat.cast_one, sub_self, zero_mul, sub_zero] at hphase
  have hkpos := Interval.phaseRoot_pos p q ℓ 1 hp hq hℓ (le_refl 1)
  simp only [Interval.mu, mass, robinForm, dirichlet]
  set k := Interval.phaseRoot p q ℓ 1 hp hq hℓ (le_refl 1) with hk
  set φ := Real.arctan (p / k) with hφ
  set ψ := Real.arctan (q / k) with hψ
  have hφpos : 0 < φ := Real.arctan_pos.2 (div_pos hp hkpos)
  have hφlt : φ < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have hψpos : 0 < ψ := Real.arctan_pos.2 (div_pos hq hkpos)
  have hψlt : ψ < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have hpos : ∀ x ∈ Icc (0 : ℝ) ℓ, 0 < Real.cos (k * x - φ) := by
    intro x hx
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · nlinarith [mul_nonneg hkpos.le hx.1]
    · nlinarith [mul_le_mul_of_nonneg_left hx.2 hkpos.le]
  have h := picone_cos hℓ.le k φ hpos (fun x => deriv u.toFun x) u.deriv_int u.deriv_sq_int
    u.toFun u.ftc
  have hw0 : -k * Real.sin (k * 0 - φ) / Real.cos (k * 0 - φ) = p := by
    have := mul_sin_div_cos_arctan p k hkpos.ne'
    rw [← hφ] at this
    simp only [mul_zero, zero_sub, Real.sin_neg, Real.cos_neg]
    rw [← this]; ring
  have hwℓ : -k * Real.sin (k * ℓ - φ) / Real.cos (k * ℓ - φ) = -q := by
    have := mul_sin_div_cos_arctan q k hkpos.ne'
    rw [← hψ] at this
    have hkℓ : k * ℓ - φ = ψ := by linarith
    rw [hkℓ, ← this]; ring
  rw [hw0, hwℓ] at h
  linarith [h]

/-! ## The second eigenvalue and its interior node -/

/-- The interior node `x₁ = (arctan (p/k₂) + π/2) / k₂` of the second eigenfunction. -/
def node (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) : ℝ :=
  (Real.arctan (p / Interval.phaseRoot p q ℓ 2 hp hq hℓ (by norm_num)) + Real.pi / 2)
    / Interval.phaseRoot p q ℓ 2 hp hq hℓ (by norm_num)

/-- The phase equation for `j = 2`: `k₂ ℓ = arctan (p/k₂) + arctan (q/k₂) + π`. -/
theorem phaseRoot_two_eq (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) :
    Interval.phaseRoot p q ℓ 2 hp hq hℓ (by norm_num) * ℓ
      = Real.arctan (p / Interval.phaseRoot p q ℓ 2 hp hq hℓ (by norm_num))
        + Real.arctan (q / Interval.phaseRoot p q ℓ 2 hp hq hℓ (by norm_num)) + Real.pi := by
  have hphase := Interval.phaseRoot_eq p q ℓ 2 hp hq hℓ (by norm_num)
  simp only [Interval.phaseFun, Nat.cast_ofNat] at hphase
  linarith [hphase]

/-- `k₂ · x₁ = arctan (p/k₂) + π/2`. -/
theorem phaseRoot_mul_node (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) :
    Interval.phaseRoot p q ℓ 2 hp hq hℓ (by norm_num) * node p q ℓ hp hq hℓ
      = Real.arctan (p / Interval.phaseRoot p q ℓ 2 hp hq hℓ (by norm_num)) + Real.pi / 2 := by
  have hkpos := Interval.phaseRoot_pos p q ℓ 2 hp hq hℓ (by norm_num)
  simp only [node]
  field_simp

/-- The node lies strictly inside `(0,ℓ)`. -/
theorem node_mem (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) :
    node p q ℓ hp hq hℓ ∈ Ioo (0 : ℝ) ℓ := by
  have hkpos := Interval.phaseRoot_pos p q ℓ 2 hp hq hℓ (by norm_num)
  have hkℓ := phaseRoot_two_eq p q ℓ hp hq hℓ
  have hkx := phaseRoot_mul_node p q ℓ hp hq hℓ
  have hφpos : 0 < Real.arctan (p / Interval.phaseRoot p q ℓ 2 hp hq hℓ (by norm_num)) :=
    Real.arctan_pos.2 (div_pos hp hkpos)
  have hψpos : 0 < Real.arctan (q / Interval.phaseRoot p q ℓ 2 hp hq hℓ (by norm_num)) :=
    Real.arctan_pos.2 (div_pos hq hkpos)
  constructor
  · simp only [node]
    exact div_pos (by linarith [Real.pi_pos]) hkpos
  · by_contra hcon
    push_neg at hcon
    have := mul_le_mul_of_nonneg_left hcon hkpos.le
    linarith [Real.pi_pos]

/-- The second eigenfunction vanishes at the node. -/
theorem phaseEigen_two_node (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) :
    phaseEigen p q ℓ 2 hp hq hℓ (by norm_num) (node p q ℓ hp hq hℓ) = 0 := by
  simp only [phaseEigen]
  rw [phaseRoot_mul_node p q ℓ hp hq hℓ]
  simp

/-- **Picone's inequality for `μ₂`**: `μ₂ · N[u] ≤ a_{p,q;ℓ}[u]` for every `u ∈ H¹(0,ℓ)`
vanishing at the node of the second eigenfunction. -/
theorem picone_two (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) (u : H1 ℓ)
    (hu : u.toFun (node p q ℓ hp hq hℓ) = 0) :
    Interval.mu p q ℓ 2 hp hq hℓ (by norm_num) * mass ℓ u ≤ robinForm p q ℓ u := by
  have hkpos := Interval.phaseRoot_pos p q ℓ 2 hp hq hℓ (by norm_num)
  have hkℓ := phaseRoot_two_eq p q ℓ hp hq hℓ
  have hkx := phaseRoot_mul_node p q ℓ hp hq hℓ
  have hx₁ := node_mem p q ℓ hp hq hℓ
  simp only [Interval.mu]
  set k := Interval.phaseRoot p q ℓ 2 hp hq hℓ (by norm_num) with hk
  set x₁ := node p q ℓ hp hq hℓ with hx₁def
  set φ := Real.arctan (p / k) with hφ
  set ψ := Real.arctan (q / k) with hψ
  -- the inequality for every `k' ∈ (0, k)`
  have hlim : ∀ k' ∈ Ioo (0 : ℝ) k, k' ^ 2 * mass ℓ u ≤ robinForm p q ℓ u := by
    intro k' hk'
    have hk'pos : 0 < k' := hk'.1
    have hk'lt : k' < k := hk'.2
    set φ' := Real.arctan (p / k') with hφ'
    set ψ' := Real.arctan (q / k') with hψ'
    have hφ'gt : φ < φ' := Real.arctan_strictMono (div_lt_div_of_pos_left hp hk'pos hk'lt)
    have hψ'gt : ψ < ψ' := Real.arctan_strictMono (div_lt_div_of_pos_left hq hk'pos hk'lt)
    have hφ'lt : φ' < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have hψ'lt : ψ' < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have hφ'pos : 0 < φ' := Real.arctan_pos.2 (div_pos hp hk'pos)
    have hψ'pos : 0 < ψ' := Real.arctan_pos.2 (div_pos hq hk'pos)
    -- left half `[0, x₁]`
    have hposL : ∀ x ∈ Icc (0 : ℝ) x₁, 0 < Real.cos (k' * x - φ') := by
      intro x hx
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · nlinarith [mul_nonneg hk'pos.le hx.1]
      · have h1 : k' * x ≤ k' * x₁ := mul_le_mul_of_nonneg_left hx.2 hk'pos.le
        have h2 : k' * x₁ < k * x₁ := mul_lt_mul_of_pos_right hk'lt hx₁.1
        linarith
    have hL := picone_cos hx₁.1.le k' φ' hposL (fun x => deriv u.toFun x)
      (H1.deriv_int_sub u le_rfl hx₁.1.le hx₁.2.le) (H1.deriv_sq_int_sub u le_rfl hx₁.1.le hx₁.2.le)
      u.toFun (H1.ftc_sub u le_rfl hx₁.1.le hx₁.2.le)
    have hw0 : -k' * Real.sin (k' * 0 - φ') / Real.cos (k' * 0 - φ') = p := by
      have := mul_sin_div_cos_arctan p k' hk'pos.ne'
      rw [← hφ'] at this
      simp only [mul_zero, zero_sub, Real.sin_neg, Real.cos_neg]
      rw [← this]; ring
    rw [hw0, hu] at hL
    -- right half `[x₁, ℓ]`, test function `cos (k' (ℓ - x) - ψ')`
    have hposR : ∀ x ∈ Icc x₁ ℓ, 0 < Real.cos (-k' * x - (ψ' - k' * ℓ)) := by
      intro x hx
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · nlinarith [mul_le_mul_of_nonneg_left hx.2 hk'pos.le]
      · have h1 : k' * x₁ ≤ k' * x := mul_le_mul_of_nonneg_left hx.1 hk'pos.le
        have h2 : k' * (ℓ - x₁) < k * (ℓ - x₁) :=
          mul_lt_mul_of_pos_right hk'lt (by linarith [hx₁.2])
        nlinarith
    have hR := picone_cos hx₁.2.le (-k') (ψ' - k' * ℓ) hposR (fun x => deriv u.toFun x)
      (H1.deriv_int_sub u hx₁.1.le hx₁.2.le le_rfl) (H1.deriv_sq_int_sub u hx₁.1.le hx₁.2.le le_rfl)
      u.toFun (H1.ftc_sub u hx₁.1.le hx₁.2.le le_rfl)
    have hwℓ : -(-k') * Real.sin (-k' * ℓ - (ψ' - k' * ℓ)) / Real.cos (-k' * ℓ - (ψ' - k' * ℓ))
        = -q := by
      have := mul_sin_div_cos_arctan q k' hk'pos.ne'
      rw [← hψ'] at this
      have harg : -k' * ℓ - (ψ' - k' * ℓ) = -ψ' := by ring
      rw [harg]
      simp only [Real.sin_neg, Real.cos_neg, neg_neg]
      rw [← this]; ring
    rw [hwℓ, hu] at hR
    -- glue the two halves
    have hmass : mass ℓ u = (∫ x in (0 : ℝ)..x₁, u.toFun x ^ 2) + ∫ x in x₁..ℓ, u.toFun x ^ 2 := by
      rw [mass]
      refine (intervalIntegral.integral_add_adjacent_intervals ?_ ?_).symm
      · exact (u.intervalIntegrable_sq).mono_set (by
          rw [uIcc_of_le hx₁.1.le, uIcc_of_le hℓ.le]; exact Icc_subset_Icc le_rfl hx₁.2.le)
      · exact (u.intervalIntegrable_sq).mono_set (by
          rw [uIcc_of_le hx₁.2.le, uIcc_of_le hℓ.le]; exact Icc_subset_Icc hx₁.1.le le_rfl)
    have hdir : dirichlet ℓ u
        = (∫ x in (0 : ℝ)..x₁, deriv u.toFun x ^ 2) + ∫ x in x₁..ℓ, deriv u.toFun x ^ 2 := by
      rw [dirichlet]
      exact (intervalIntegral.integral_add_adjacent_intervals
        (H1.deriv_sq_int_sub u le_rfl hx₁.1.le hx₁.2.le)
        (H1.deriv_sq_int_sub u hx₁.1.le hx₁.2.le le_rfl)).symm
    rw [hmass, robinForm, hdir]
    have hsq : (-k') ^ 2 = k' ^ 2 := by ring
    rw [hsq] at hR
    nlinarith [hL, hR]
  -- pass to the limit `k' → k`
  have hev : ∀ᶠ k' in 𝓝[<] k, k' ^ 2 * mass ℓ u ≤ robinForm p q ℓ u :=
    Filter.mem_of_superset (Ioo_mem_nhdsLT hkpos) fun k' hk' => hlim k' hk'
  have htend : Tendsto (fun k' : ℝ => k' ^ 2 * mass ℓ u) (𝓝[<] k) (𝓝 (k ^ 2 * mass ℓ u)) :=
    ((continuous_id.pow 2).mul continuous_const).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  exact le_of_tendsto htend hev

end

end RobinCaps.Sobolev.Picone
