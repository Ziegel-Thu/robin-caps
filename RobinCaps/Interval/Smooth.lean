import RobinCaps.Interval.Phase
import RobinCaps.Interval.Gap

/-!
# Smooth and Lipschitz dependence of the interval Robin eigenvalues on the parameters

This file formalizes the second half of Lemma 3.1 (`lem:interval`) of
`reference/robin_endcaps_corrected_en.tex` and its consequence `eq:interval-O-R`.

For `p q ℓ > 0` and `j ≥ 1`, the `j`-th interval Robin eigenvalue is `μ_j(p,q;ℓ) = k_j²`,
where `k_j = phaseRoot p q ℓ j …` is the unique positive root of the phase function
`H_j(k) = kℓ - arctan(p/k) - arctan(q/k) - (j-1)π` (see `RobinCaps.Interval.Phase`).

* `root j` / `muFun j` are total functions `ℝ × ℝ × ℝ → ℝ` agreeing with
  `phaseRoot` / `mu` on the open positive octant (`root_eq`, `muFun_eq`).
* `phaseFun_hasDerivAt` is the derivative formula `eq:phase-derivative`
  `∂_k H_j = ℓ + p/(k²+p²) + q/(k²+q²)`, which is strictly positive.
* `root_contDiffAt` / `muFun_contDiffAt`: the root and the eigenvalue are `C^n` (for every
  `n : WithTop ℕ∞`, including `ω`) at every point of the positive octant.  This is the
  implicit function theorem (`IsContDiffImplicitAt` from
  `Mathlib.Analysis.Calculus.ImplicitContDiff`), applied to the four-variable phase function
  `Phi j (p,q,ℓ,k) = phaseFun p q ℓ j k`; the implicit function is identified with `root j`
  near the base point by uniqueness of the positive root (`existsUnique_phaseRoot`).
* `muFun_lipschitzOnWith_Icc`: `μ_j` is Lipschitz on every box `Icc a b ⊂ (0,∞)³`
  (compact and convex), by the mean value inequality with a bounded derivative.
* `mu_perturbation_bound` (`eq:interval-O-R`): an explicit local Lipschitz estimate
  `|μ_j(p',q';ℓ') - μ_j(p,q;L)| ≤ C (|p'-p| + |q'-q| + |ℓ'-L|)` for `(p',q',ℓ')` in a
  `δ`-box around `(p,q,L)`.
-/

open Set Filter
open scoped Topology NNReal

namespace RobinCaps.Interval

noncomputable section

/-! ### Total versions of the root and of the eigenvalue -/

/-- The phase root as a total function of the parameter triple `(p, q, ℓ)`; it is `0` outside
the positive octant or for `j = 0`. -/
def root (j : ℕ) (x : ℝ × ℝ × ℝ) : ℝ :=
  if h : 0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2 ∧ 1 ≤ j then
    phaseRoot x.1 x.2.1 x.2.2 j h.1 h.2.1 h.2.2.1 h.2.2.2
  else 0

/-- The eigenvalue `μ_j = k_j²` as a total function of the parameter triple `(p, q, ℓ)`. -/
def muFun (j : ℕ) (x : ℝ × ℝ × ℝ) : ℝ :=
  root j x ^ 2

theorem root_eq (j : ℕ) (hj : 1 ≤ j) {x : ℝ × ℝ × ℝ}
    (hx : 0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2) :
    root j x = phaseRoot x.1 x.2.1 x.2.2 j hx.1 hx.2.1 hx.2.2 hj :=
  dif_pos ⟨hx.1, hx.2.1, hx.2.2, hj⟩

theorem root_mk (j : ℕ) (hj : 1 ≤ j) (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) :
    root j (p, q, ℓ) = phaseRoot p q ℓ j hp hq hℓ hj :=
  root_eq j hj ⟨hp, hq, hℓ⟩

theorem muFun_eq (j : ℕ) (hj : 1 ≤ j) {x : ℝ × ℝ × ℝ}
    (hx : 0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2) :
    muFun j x = mu x.1 x.2.1 x.2.2 j hx.1 hx.2.1 hx.2.2 hj := by
  simp only [muFun, mu, root_eq j hj hx]

theorem muFun_mk (j : ℕ) (hj : 1 ≤ j) (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) :
    muFun j (p, q, ℓ) = mu p q ℓ j hp hq hℓ hj :=
  muFun_eq j hj ⟨hp, hq, hℓ⟩

theorem root_pos (j : ℕ) (hj : 1 ≤ j) {x : ℝ × ℝ × ℝ}
    (hx : 0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2) : 0 < root j x := by
  rw [root_eq j hj hx]
  exact phaseRoot_pos _ _ _ _ _ _ _ _

theorem root_phaseFun_eq_zero (j : ℕ) (hj : 1 ≤ j) {x : ℝ × ℝ × ℝ}
    (hx : 0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2) :
    phaseFun x.1 x.2.1 x.2.2 j (root j x) = 0 := by
  rw [root_eq j hj hx]
  exact phaseRoot_eq _ _ _ _ _ _ _ _

/-! ### The derivative of the phase function in `k` (`eq:phase-derivative`) -/

/-- `∂_k H_j(k) = ℓ + p/(k²+p²) + q/(k²+q²)` for `k > 0`. -/
theorem phaseFun_hasDerivAt (p q ℓ : ℝ) (j : ℕ) {k : ℝ} (hk : 0 < k) :
    HasDerivAt (phaseFun p q ℓ j)
      (ℓ + p / (k ^ 2 + p ^ 2) + q / (k ^ 2 + q ^ 2)) k := by
  have hkne : k ≠ 0 := hk.ne'
  have h1 : HasDerivAt (fun y : ℝ => y * ℓ) (1 * ℓ) k := (hasDerivAt_id k).mul_const ℓ
  have hp : HasDerivAt (fun y : ℝ => Real.arctan (p * y⁻¹))
      (1 / (1 + (p * k⁻¹) ^ 2) * (p * -(k ^ 2)⁻¹)) k :=
    ((hasDerivAt_inv hkne).const_mul p).arctan
  have hq : HasDerivAt (fun y : ℝ => Real.arctan (q * y⁻¹))
      (1 / (1 + (q * k⁻¹) ^ 2) * (q * -(k ^ 2)⁻¹)) k :=
    ((hasDerivAt_inv hkne).const_mul q).arctan
  have h := ((h1.fun_sub hp).fun_sub hq).sub_const (((j : ℝ) - 1) * Real.pi)
  have hfun : phaseFun p q ℓ j = fun y : ℝ =>
      y * ℓ - Real.arctan (p * y⁻¹) - Real.arctan (q * y⁻¹) - ((j : ℝ) - 1) * Real.pi := by
    funext y
    simp only [phaseFun, div_eq_mul_inv]
  rw [hfun]
  refine h.congr_deriv ?_
  have hk2 : (k ^ 2 + p ^ 2) ≠ 0 := by positivity
  have hq2 : (k ^ 2 + q ^ 2) ≠ 0 := by positivity
  field_simp
  ring

/-- The derivative `eq:phase-derivative` is strictly positive when `p q ℓ > 0`. -/
theorem phaseDeriv_pos {p q ℓ k : ℝ} (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) :
    0 < ℓ + p / (k ^ 2 + p ^ 2) + q / (k ^ 2 + q ^ 2) := by
  positivity

/-! ### The phase function in all four variables -/

/-- The phase function as a function of all four variables `((p, q, ℓ), k)`. -/
def Phi (j : ℕ) (v : (ℝ × ℝ × ℝ) × ℝ) : ℝ :=
  phaseFun v.1.1 v.1.2.1 v.1.2.2 j v.2

/-- `Phi j` is `C^n` (for every `n`, including `ω`) at every point with `k ≠ 0`. -/
theorem Phi_contDiffAt (j : ℕ) {n : WithTop ℕ∞} {v : (ℝ × ℝ × ℝ) × ℝ} (hv : v.2 ≠ 0) :
    ContDiffAt ℝ n (Phi j) v := by
  have hk : ContDiffAt ℝ n (fun w : (ℝ × ℝ × ℝ) × ℝ => w.2) v := contDiffAt_snd
  have hp : ContDiffAt ℝ n (fun w : (ℝ × ℝ × ℝ) × ℝ => w.1.1) v :=
    contDiffAt_fst.comp v contDiffAt_fst
  have hq : ContDiffAt ℝ n (fun w : (ℝ × ℝ × ℝ) × ℝ => w.1.2.1) v :=
    contDiffAt_fst.comp v (contDiffAt_snd.comp v contDiffAt_fst)
  have hℓ : ContDiffAt ℝ n (fun w : (ℝ × ℝ × ℝ) × ℝ => w.1.2.2) v :=
    contDiffAt_snd.comp v (contDiffAt_snd.comp v contDiffAt_fst)
  have h1 : ContDiffAt ℝ n (fun w : (ℝ × ℝ × ℝ) × ℝ => w.2 * w.1.2.2) v := hk.mul hℓ
  have h2 : ContDiffAt ℝ n (fun w : (ℝ × ℝ × ℝ) × ℝ => Real.arctan (w.1.1 / w.2)) v :=
    Real.contDiff_arctan.contDiffAt.comp v (hp.div hk hv)
  have h3 : ContDiffAt ℝ n (fun w : (ℝ × ℝ × ℝ) × ℝ => Real.arctan (w.1.2.1 / w.2)) v :=
    Real.contDiff_arctan.contDiffAt.comp v (hq.div hk hv)
  have h4 : ContDiffAt ℝ n (fun _ : (ℝ × ℝ × ℝ) × ℝ => ((j : ℝ) - 1) * Real.pi) v :=
    contDiffAt_const
  exact ((h1.sub h2).sub h3).sub h4

/-! ### Smooth dependence of the root (implicit function theorem) -/

/-- **Smooth dependence of the phase root** (`lem:interval`, second half), analytic version:
`root j` is `C^ω` (hence `C^n` for every `n`) at every point of the open positive octant. -/
theorem root_contDiffAt_top (j : ℕ) (hj : 1 ≤ j) {x : ℝ × ℝ × ℝ}
    (hx : 0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2) :
    ContDiffAt ℝ ⊤ (root j) x := by
  set k₀ := root j x with hk₀
  have hk₀pos : 0 < k₀ := root_pos j hj hx
  have hroot : Phi j (x, k₀) = 0 := root_phaseFun_eq_zero j hj hx
  have hcd : ContDiffAt ℝ ⊤ (Phi j) (x, k₀) := Phi_contDiffAt j hk₀pos.ne'
  have hdiff : HasFDerivAt (Phi j) (fderiv ℝ (Phi j) (x, k₀)) (x, k₀) :=
    (hcd.differentiableAt le_top).hasFDerivAt
  set f' := fderiv ℝ (Phi j) (x, k₀) with hf'
  set d := x.2.2 + x.1 / (k₀ ^ 2 + x.1 ^ 2) + x.2.1 / (k₀ ^ 2 + x.2.1 ^ 2) with hd
  have hdpos : 0 < d := phaseDeriv_pos hx.1 hx.2.1 hx.2.2
  -- the partial derivative in `k` is `d`
  have hf'01 : f' ((0 : ℝ × ℝ × ℝ), (1 : ℝ)) = d := by
    have hcurve : HasDerivAt (fun k : ℝ => ((x, k) : (ℝ × ℝ × ℝ) × ℝ))
        (((0 : ℝ × ℝ × ℝ), (1 : ℝ))) k₀ :=
      (hasDerivAt_const k₀ x).prodMk (hasDerivAt_id k₀)
    have h1 : HasDerivAt (fun k : ℝ => Phi j (x, k)) (f' ((0 : ℝ × ℝ × ℝ), (1 : ℝ))) k₀ :=
      hdiff.comp_hasDerivAt_of_eq k₀ hcurve rfl
    have h2 : HasDerivAt (fun k : ℝ => Phi j (x, k)) d k₀ :=
      phaseFun_hasDerivAt x.1 x.2.1 x.2.2 j hk₀pos
    exact h1.unique h2
  -- hence the derivative in the `k`-direction is bijective
  have hlin : ∀ t : ℝ, (f'.comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ × ℝ) ℝ)) t = t * d := by
    intro t
    have hsmul : (((0 : ℝ × ℝ × ℝ), t) : (ℝ × ℝ × ℝ) × ℝ)
        = t • (((0 : ℝ × ℝ × ℝ), (1 : ℝ)) : (ℝ × ℝ × ℝ) × ℝ) := by
      simp
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    rw [hsmul, map_smul, hf'01, smul_eq_mul]
  have hbij : Function.Bijective (f'.comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ × ℝ) ℝ)) := by
    constructor
    · intro s t hst
      rw [hlin, hlin] at hst
      exact mul_right_cancel₀ hdpos.ne' hst
    · intro z
      refine ⟨z / d, ?_⟩
      rw [hlin]
      field_simp
  have himp : IsContDiffImplicitAt (⊤ : WithTop ℕ∞) (Phi j) f' (x, k₀) :=
    ⟨hdiff, hcd, hbij, le_top⟩
  set g := himp.implicitFunction with hg
  have hgcd : ContDiffAt ℝ ⊤ g x := himp.contDiffAt_implicitFunction
  -- the implicit function takes the value `k₀` at `x`
  have hgx : g x = k₀ := by
    have h := himp.implicitFunctionData.implicitFunction_apply_image.self_of_nhds
    exact congrArg Prod.snd h
  -- near `x`, the implicit function is a positive root, hence equals `root j`
  have hev1 : ∀ᶠ y in 𝓝 x, Phi j (y, g y) = 0 :=
    himp.apply_implicitFunction.mono fun y hy => hy.trans hroot
  have hev2 : ∀ᶠ y in 𝓝 x, 0 < g y :=
    continuousAt_const.eventually_lt hgcd.continuousAt (by rw [hgx]; exact hk₀pos)
  have hev3 : ∀ᶠ y in 𝓝 x, 0 < y.1 ∧ 0 < y.2.1 ∧ 0 < y.2.2 := by
    have h1 : ∀ᶠ y in 𝓝 x, 0 < y.1 :=
      continuousAt_const.eventually_lt continuous_fst.continuousAt hx.1
    have h2 : ∀ᶠ y in 𝓝 x, 0 < y.2.1 :=
      continuousAt_const.eventually_lt continuous_snd.fst.continuousAt hx.2.1
    have h3 : ∀ᶠ y in 𝓝 x, 0 < y.2.2 :=
      continuousAt_const.eventually_lt continuous_snd.snd.continuousAt hx.2.2
    exact h1.and (h2.and h3)
  have heq : root j =ᶠ[𝓝 x] g := by
    filter_upwards [hev1, hev2, hev3] with y hy1 hy2 hy3
    rw [root_eq j hj hy3]
    exact (existsUnique_phaseRoot y.1 y.2.1 y.2.2 hy3.1 hy3.2.1 hy3.2.2 j hj).unique
      ⟨phaseRoot_pos _ _ _ _ _ _ _ _, phaseRoot_eq _ _ _ _ _ _ _ _⟩ ⟨hy2, hy1⟩
  exact hgcd.congr_of_eventuallyEq heq

/-- **Smooth dependence of the phase root** (`lem:interval`, second half): `root j` is `C^n`
for every `n : WithTop ℕ∞` at every point of the open positive octant. -/
theorem root_contDiffAt (j : ℕ) (hj : 1 ≤ j) (n : WithTop ℕ∞) {x : ℝ × ℝ × ℝ}
    (hx : 0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2) :
    ContDiffAt ℝ n (root j) x :=
  (root_contDiffAt_top j hj hx).of_le le_top

theorem root_differentiableAt (j : ℕ) (hj : 1 ≤ j) {x : ℝ × ℝ × ℝ}
    (hx : 0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2) :
    DifferentiableAt ℝ (root j) x :=
  (root_contDiffAt j hj 1 hx).differentiableAt le_rfl

/-- **Smooth dependence of the eigenvalue** (`lem:interval`, second half): `μ_j` is `C^n` for
every `n : WithTop ℕ∞` at every point of the open positive octant. -/
theorem muFun_contDiffAt (j : ℕ) (hj : 1 ≤ j) (n : WithTop ℕ∞) {x : ℝ × ℝ × ℝ}
    (hx : 0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2) :
    ContDiffAt ℝ n (muFun j) x :=
  (root_contDiffAt j hj n hx).pow 2

theorem muFun_differentiableAt (j : ℕ) (hj : 1 ≤ j) {x : ℝ × ℝ × ℝ}
    (hx : 0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2) :
    DifferentiableAt ℝ (muFun j) x :=
  (muFun_contDiffAt j hj 1 hx).differentiableAt le_rfl

/-! ### Lipschitz dependence on compact boxes -/

/-- Points of a box `Icc a b` with `a` in the positive octant lie in the positive octant. -/
theorem pos_of_mem_Icc {a b x : ℝ × ℝ × ℝ} (ha : 0 < a.1 ∧ 0 < a.2.1 ∧ 0 < a.2.2)
    (hx : x ∈ Icc a b) : 0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2 := by
  obtain ⟨hax, _⟩ := hx
  have h1 := Prod.le_def.mp hax
  have h2 := Prod.le_def.mp h1.2
  exact ⟨lt_of_lt_of_le ha.1 h1.1, lt_of_lt_of_le ha.2.1 h2.1, lt_of_lt_of_le ha.2.2 h2.2⟩

/-- **Lipschitz dependence** (`lem:interval`, "Lipschitz on every compact parameter set"):
`μ_j` is Lipschitz on every box `Icc a b` whose lower corner lies in the positive octant. -/
theorem muFun_lipschitzOnWith_Icc (j : ℕ) (hj : 1 ≤ j) (a b : ℝ × ℝ × ℝ)
    (ha : 0 < a.1 ∧ 0 < a.2.1 ∧ 0 < a.2.2) :
    ∃ C : ℝ≥0, LipschitzOnWith C (muFun j) (Icc a b) := by
  have hcd : ∀ x ∈ Icc a b, ContDiffAt ℝ ⊤ (muFun j) x :=
    fun x hx => muFun_contDiffAt j hj ⊤ (pos_of_mem_Icc ha hx)
  have hdiff : ∀ x ∈ Icc a b, DifferentiableAt ℝ (muFun j) x :=
    fun x hx => (hcd x hx).differentiableAt le_top
  have hcont : ContinuousOn (fun x => fderiv ℝ (muFun j) x) (Icc a b) :=
    fun x hx => ((hcd x hx).continuousAt_fderiv WithTop.top_ne_zero).continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨⟨max C 0, le_max_right _ _⟩, ?_⟩
  refine (convex_Icc a b).lipschitzOnWith_of_nnnorm_fderiv_le hdiff ?_
  intro x hx
  rw [← NNReal.coe_le_coe]
  simp only [coe_nnnorm, NNReal.coe_mk]
  exact le_trans (hC x hx) (le_max_left _ _)

/-! ### The `O(R)` estimate `eq:interval-O-R` -/

/-- **`eq:interval-O-R`, explicit form.** For `p q L > 0` there are `C` and `δ > 0` such that
for all `(p', q', ℓ')` within `δ` of `(p, q, L)` (componentwise),
`|μ_j(p',q';ℓ') - μ_j(p,q;L)| ≤ C (|p'-p| + |q'-q| + |ℓ'-L|)`. -/
theorem mu_perturbation_bound (j : ℕ) (hj : 1 ≤ j) (p q L : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hL : 0 < L) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ p' q' ℓ' : ℝ, |p' - p| ≤ δ → |q' - q| ≤ δ → |ℓ' - L| ≤ δ →
      ∀ (hp' : 0 < p') (hq' : 0 < q') (hℓ' : 0 < ℓ'),
        |mu p' q' ℓ' j hp' hq' hℓ' hj - mu p q L j hp hq hL hj|
          ≤ C * (|p' - p| + |q' - q| + |ℓ' - L|) := by
  set δ := min p (min q L) / 2 with hδ
  have hmin : 0 < min p (min q L) := lt_min hp (lt_min hq hL)
  have hδpos : 0 < δ := by positivity
  have hδp : δ < p := by
    have := min_le_left p (min q L)
    linarith
  have hδq : δ < q := by
    have := le_trans (min_le_right p (min q L)) (min_le_left q L)
    linarith
  have hδL : δ < L := by
    have := le_trans (min_le_right p (min q L)) (min_le_right q L)
    linarith
  set a : ℝ × ℝ × ℝ := (p - δ, q - δ, L - δ) with ha_def
  set b : ℝ × ℝ × ℝ := (p + δ, q + δ, L + δ) with hb_def
  have ha : 0 < a.1 ∧ 0 < a.2.1 ∧ 0 < a.2.2 := by
    simp only [ha_def]
    exact ⟨by linarith, by linarith, by linarith⟩
  obtain ⟨C, hC⟩ := muFun_lipschitzOnWith_Icc j hj a b ha
  refine ⟨(C : ℝ), δ, hδpos, ?_⟩
  intro p' q' ℓ' hp'' hq'' hℓ'' hp' hq' hℓ'
  have hmem : ∀ {p' q' ℓ' : ℝ}, |p' - p| ≤ δ → |q' - q| ≤ δ → |ℓ' - L| ≤ δ →
      ((p', q', ℓ') : ℝ × ℝ × ℝ) ∈ Icc a b := by
    intro p' q' ℓ' h1 h2 h3
    rw [abs_le] at h1 h2 h3
    refine ⟨?_, ?_⟩
    · simp only [ha_def, Prod.mk_le_mk]
      exact ⟨by linarith, by linarith, by linarith⟩
    · simp only [hb_def, Prod.mk_le_mk]
      exact ⟨by linarith, by linarith, by linarith⟩
  have hy' : ((p', q', ℓ') : ℝ × ℝ × ℝ) ∈ Icc a b := hmem hp'' hq'' hℓ''
  have hy : ((p, q, L) : ℝ × ℝ × ℝ) ∈ Icc a b :=
    hmem (by simp [hδpos.le]) (by simp [hδpos.le]) (by simp [hδpos.le])
  have hd := hC.dist_le_mul _ hy' _ hy
  rw [← muFun_mk j hj p' q' ℓ' hp' hq' hℓ', ← muFun_mk j hj p q L hp hq hL, ← Real.dist_eq]
  refine le_trans hd ?_
  apply mul_le_mul_of_nonneg_left _ C.coe_nonneg
  simp only [Prod.dist_eq, Real.dist_eq]
  have h1 := abs_nonneg (p' - p)
  have h2 := abs_nonneg (q' - q)
  have h3 := abs_nonneg (ℓ' - L)
  apply max_le
  · linarith
  · apply max_le
    · linarith
    · linarith

end

end RobinCaps.Interval
