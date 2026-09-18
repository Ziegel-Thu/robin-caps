import RobinCaps.Sobolev.VariationBridge

set_option linter.style.longLine false

/-!
# U-SOB-3: the quotient Sobolev space `H¹(0,ℓ) ⧸ N` and the min–max upper half `λ_j ≤ μ_j`

`RobinCaps/Sobolev/VariationBridge.lean` records two obstructions to running the abstract
form engine `RobinCaps.Spectrum.minmax` on the whole model space `H1 ℓ`:

(a) `mass ℓ` is not positive definite on `H1 ℓ` (functions supported off `[0,ℓ]` are nonzero
    with zero mass), and
(b) `BddAboveRatio (robinForm p q ℓ) (mass ℓ)` fails (the Robin spectrum is unbounded above).

This file fixes both.

## Part A — engine extension (namespace `RobinCaps.Spectrum`)

* `minmax_le_of_trial'` — the trial-space upper bound **without** `BddAboveRatio`.  The
  only place the old proof used the upper ratio bound was to bound the outer family
  `V ↦ ⨆ ratio` from below; but in `ℝ` an unbounded `iSup` is `0` by convention
  (`Real.iSup_of_not_bddAbove`), which is still `≥ c` for the nonpositive constant `c`
  of `BddBelowRatio`.
* `le_minmax_of_codim'` — the codimension lower bound with the global `BddAboveRatio`
  replaced by boundedness of the ratio on every `j`-dimensional subspace.
* `bddAbove_ratio_of_bilinear` — for quadratic forms `q u = Q u u`, `b u = B u u` coming from
  bilinear maps, with `B` positive definite, the ratio `q / b` is bounded above on every
  finite-dimensional subspace (compactness of the unit sphere in coordinates).

## Part B — the quotient space (namespace `RobinCaps.Sobolev`)

* `nullOff ℓ` — the subspace of `H1 ℓ` of functions vanishing on `[0,ℓ]` (we use the
  unordered interval `uIcc 0 ℓ`, which is `Icc 0 ℓ` for `ℓ ≥ 0`, so that all descents are
  unconditional in `ℓ`), and `H1Q ℓ := H1 ℓ ⧸ nullOff ℓ`.
* The Robin and mass bilinear forms descend to `H1Q ℓ` (`robinBilinQ`, `massBilinQ`), giving
  `robinFormQ`, `massQ`, `robinMinmaxQ p q ℓ j := minmax (robinFormQ p q ℓ) (massQ ℓ) j`, and
  `massQ_pos` (positive definiteness on the quotient, for `ℓ > 0`).
* **Upper half for every `j ≥ 1`**: `robinMinmaxQ_le_mu`, via the trial space spanned by the
  images of the first `j` phase eigenfunctions.
* **Lower half wrapper**: `mu_le_robinMinmaxQ_of_picone`, taking the Picone-type inequality
  `μ_j · mass u ≤ robinForm u` on `ker φ` as a hypothesis, with specialisations to `j = 1`
  and to `j = 2` with `φ = evalAt x₁`.

Everything below is proved without `sorry`, `axiom` or `admit`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Set Filter
open scoped Topology Interval

/-! ## Part A: engine extension -/

namespace RobinCaps.Spectrum

variable {H : Type*} [AddCommGroup H] [Module ℝ H]

/-- The outer family `V ↦ ⨆ u ∈ V∖{0}, q u / b u` is bounded below by the constant of
`BddBelowRatio`, **without** any upper ratio bound: if the inner range is unbounded above,
the real `iSup` is `0`, which is still `≥ c ≤ 0`. -/
theorem bddBelow_range_minmaxFamily' (q b : H → ℝ) (hB : BddBelowRatio q b) (j : ℕ) :
    BddBelow (Set.range fun V : {V : Submodule ℝ H // Module.finrank ℝ V = j} =>
      ⨆ u : {u : V.1 // u ≠ 0}, q ((u : V.1) : H) / b ((u : V.1) : H)) := by
  obtain ⟨c, hc0, hc⟩ := hB
  refine ⟨c, ?_⟩
  rintro y ⟨V, rfl⟩
  change c ≤ ⨆ u : {u : V.1 // u ≠ 0}, q ((u : V.1) : H) / b ((u : V.1) : H)
  rcases isEmpty_or_nonempty {u : V.1 // u ≠ 0} with hempty | hne
  · haveI := hempty
    rw [iSup_of_empty']
    simpa using hc0
  · by_cases hbdd : BddAbove (Set.range fun u : {u : V.1 // u ≠ 0} =>
        q ((u : V.1) : H) / b ((u : V.1) : H))
    · exact le_trans (hc _ (fun hh => hne.some.2 (Subtype.ext hh)))
        (le_ciSup hbdd hne.some)
    · rw [Real.iSup_of_not_bddAbove hbdd]
      exact hc0

/-- **Trial-space upper bound without `BddAboveRatio`.**  If `W` is a `j`-dimensional
subspace (`j > 0`) on which `q ≤ t · b`, then `minmax q b j ≤ t`.  Only the lower ratio
bound `BddBelowRatio q b` is needed. -/
theorem minmax_le_of_trial' (q b : H → ℝ) (j : ℕ) (hj : 0 < j)
    (hb : ∀ u, u ≠ 0 → 0 < b u) (hB : BddBelowRatio q b)
    (W : Submodule ℝ H) (hW : Module.finrank ℝ W = j) (t : ℝ)
    (h : ∀ u ∈ W, u ≠ 0 → q u ≤ t * b u) : minmax q b j ≤ t := by
  have hfin : 0 < Module.finrank ℝ W := by rw [hW]; exact hj
  haveI : Nontrivial W := Module.nontrivial_of_finrank_pos hfin
  haveI : Nonempty {u : W // u ≠ 0} := by
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    exact ⟨⟨w, hw⟩⟩
  unfold minmax
  refine ciInf_le_of_le (bddBelow_range_minmaxFamily' q b hB j) ⟨W, hW⟩ ?_
  apply ciSup_le
  intro u
  have huW : ((u : W) : H) ∈ W := (u : W).2
  have hune : ((u : W) : H) ≠ 0 := fun hh => u.2 (Subtype.ext hh)
  rw [div_le_iff₀ (hb _ hune)]
  exact h _ huW hune

/-- **Finite-codimension lower bound with per-subspace boundedness.**  Same as
`le_minmax_of_codim`, but the global `BddAboveRatio q b` is replaced by boundedness of the
ratio on each `j`-dimensional subspace (hypothesis `hA`). -/
theorem le_minmax_of_codim' (q b : H → ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hb : ∀ u, u ≠ 0 → 0 < b u)
    (hA : ∀ V : Submodule ℝ H, Module.finrank ℝ V = j →
      BddAbove (Set.range fun u : {u : V // u ≠ 0} => q ((u : V) : H) / b ((u : V) : H)))
    (φ : H →ₗ[ℝ] (Fin (j - 1) → ℝ))
    (hφ : Module.finrank ℝ (LinearMap.range φ) = j - 1) (t : ℝ)
    (h : ∀ u : H, u ≠ 0 → φ u = 0 → t * b u ≤ q u)
    (hex : ∃ V : Submodule ℝ H, Module.finrank ℝ V = j) :
    t ≤ minmax q b j := by
  haveI : Nonempty {V : Submodule ℝ H // Module.finrank ℝ V = j} := by
    obtain ⟨V, hV⟩ := hex
    exact ⟨⟨V, hV⟩⟩
  unfold minmax
  apply le_ciInf
  intro V
  set W : Submodule ℝ H := V.1 with hWdef
  have hWfin : Module.finrank ℝ W = j := by rw [hWdef]; exact V.2
  haveI : FiniteDimensional ℝ W :=
    FiniteDimensional.of_finrank_pos (by rw [hWfin]; omega)
  let ψ : W →ₗ[ℝ] (Fin (j - 1) → ℝ) := φ.comp W.subtype
  have hrangeψ : LinearMap.range ψ = Submodule.map φ W := by
    change LinearMap.range (φ.comp W.subtype) = Submodule.map φ W
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hle : Module.finrank ℝ ↥(LinearMap.range ψ) ≤ j - 1 := by
    rw [hrangeψ]
    calc Module.finrank ℝ ↥(Submodule.map φ W)
        ≤ Module.finrank ℝ ↥(LinearMap.range φ) := by
          apply Submodule.finrank_mono
          rw [Submodule.map_le_iff_le_comap]
          intro x _
          exact ⟨x, rfl⟩
      _ = j - 1 := hφ
  have hker : 1 ≤ Module.finrank ℝ ↥(LinearMap.ker ψ) := by
    have hrk := LinearMap.finrank_range_add_finrank_ker ψ
    have hle' : Module.finrank ℝ ↥(LinearMap.range ψ) ≤ Module.finrank ℝ W - 1 := by
      rw [hWfin]; exact hle
    omega
  haveI : Nontrivial ↥(LinearMap.ker ψ) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (M := ↥(LinearMap.ker ψ)) (by omega)
  obtain ⟨w, hwne0⟩ := exists_ne (0 : ↥(LinearMap.ker ψ))
  have hwne : w.1 ≠ (0 : W) := fun h0 => hwne0 (Subtype.ext h0)
  have hwker : w.1 ∈ LinearMap.ker ψ := w.2
  have hphi : φ ((w.1 : W) : H) = 0 := by
    have hmem := LinearMap.mem_ker.mp hwker
    simpa only [ψ, LinearMap.comp_apply, Submodule.subtype_apply] using hmem
  have hwHne : ((w.1 : W) : H) ≠ 0 := fun hh => hwne (Subtype.ext hh)
  have hlow : t ≤ q ((w.1 : W) : H) / b ((w.1 : W) : H) := by
    rw [le_div_iff₀ (hb _ hwHne)]
    exact h ((w.1 : W) : H) hwHne hphi
  exact le_trans hlow (le_ciSup (hA W hWfin) ⟨w.1, hwne⟩)

/-- **Boundedness of the ratio of two quadratic forms on a finite-dimensional subspace.**
If `Q B : H →ₗ[ℝ] H →ₗ[ℝ] ℝ` are bilinear and `B` is positive definite, then on every
finite-dimensional subspace `V` the ratio `Q u u / B u u` (over `u ∈ V ∖ {0}`) is bounded
above.  Proof: in coordinates `Fin n → ℝ` given by a basis of `V`, the ratio is a
continuous function on the compact unit sphere, hence bounded there, and it is invariant
under scaling. -/
theorem bddAbove_ratio_of_bilinear (Q B : H →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (hB : ∀ u : H, u ≠ 0 → 0 < B u u) (V : Submodule ℝ H) [FiniteDimensional ℝ V] :
    BddAbove (Set.range fun u : {u : V // u ≠ 0} =>
      Q ((u : V) : H) ((u : V) : H) / B ((u : V) : H) ((u : V) : H)) := by
  classical
  set n := Module.finrank ℝ V with hn
  let e : Module.Basis (Fin n) ℝ V := Module.finBasis ℝ V
  let φ : (Fin n → ℝ) →ₗ[ℝ] H := V.subtype.comp (e.equivFun.symm : (Fin n → ℝ) →ₗ[ℝ] V)
  -- continuity of `c ↦ M (φ c) (φ c)` for any bilinear `M`
  have hcont : ∀ M : H →ₗ[ℝ] H →ₗ[ℝ] ℝ, Continuous fun c : Fin n → ℝ => M (φ c) (φ c) := by
    intro M
    have hexp : ∀ x y : Fin n → ℝ, M (φ x) (φ y)
        = ∑ i, x i * M (φ (fun j => if i = j then (1 : ℝ) else 0)) (φ y) := by
      intro x y
      have h := congrArg (fun z => M (φ z) (φ y)) (pi_eq_sum_univ x)
      simpa only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
        smul_eq_mul] using h
    have hfun : (fun c : Fin n → ℝ => M (φ c) (φ c))
        = fun c => ∑ i, c i * M (φ (fun j => if i = j then (1 : ℝ) else 0)) (φ c) :=
      funext fun c => hexp c c
    rw [hfun]
    apply continuous_finset_sum
    intro i _
    exact (continuous_apply i).mul
      (LinearMap.continuous_of_finiteDimensional
        ((M (φ (fun j => if i = j then (1 : ℝ) else 0))).comp φ))
  -- nonvanishing of `φ` off the origin
  have hφne : ∀ c : Fin n → ℝ, c ≠ 0 → φ c ≠ 0 := by
    intro c hc hφc
    apply hc
    have h1 : e.equivFun.symm c = 0 := by
      apply Subtype.ext
      simpa [φ] using hφc
    have h2 := congrArg e.equivFun h1
    rwa [LinearEquiv.apply_symm_apply, map_zero] at h2
  -- the ratio on the unit sphere is bounded
  set S : Set (Fin n → ℝ) := Metric.sphere (0 : Fin n → ℝ) 1 with hS
  have hSne : ∀ c ∈ S, c ≠ 0 := by
    intro c hc h0
    rw [hS, mem_sphere_zero_iff_norm] at hc
    rw [h0, norm_zero] at hc
    exact zero_ne_one hc
  have hcontOn : ContinuousOn (fun c : Fin n → ℝ => Q (φ c) (φ c) / B (φ c) (φ c)) S :=
    (hcont Q).continuousOn.div (hcont B).continuousOn
      (fun c hc => ne_of_gt (hB _ (hφne c (hSne c hc))))
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : Fin n → ℝ) 1).bddAbove_image hcontOn
  refine ⟨C, ?_⟩
  rintro y ⟨u, rfl⟩
  -- scale `u` to the unit sphere in coordinates
  set c : Fin n → ℝ := e.equivFun (u : V) with hc
  have hcne : c ≠ 0 := by
    intro h0
    apply u.2
    have := congrArg e.equivFun.symm h0
    rwa [hc, LinearEquiv.symm_apply_apply, map_zero] at this
  have hnorm : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hcne
  set a : ℝ := ‖c‖⁻¹ with ha
  have hane : a ≠ 0 := inv_ne_zero hnorm
  have hmemS : a • c ∈ S := by
    rw [hS, mem_sphere_zero_iff_norm, norm_smul, ha, norm_inv, norm_norm,
      inv_mul_cancel₀ hnorm]
  have hφac : φ (a • c) = a • ((u : V) : H) := by
    simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe, map_smul, hc,
      LinearEquiv.symm_apply_apply, Submodule.subtype_apply]
  have hval : Q (φ (a • c)) (φ (a • c)) / B (φ (a • c)) (φ (a • c))
      = Q ((u : V) : H) ((u : V) : H) / B ((u : V) : H) ((u : V) : H) := by
    rw [hφac]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [← mul_assoc, ← mul_assoc]
    exact mul_div_mul_left _ _ (mul_ne_zero hane hane)
  show Q ((u : V) : H) ((u : V) : H) / B ((u : V) : H) ((u : V) : H) ≤ C
  rw [← hval]
  exact hC ⟨a • c, hmemS, rfl⟩

end RobinCaps.Spectrum

/-! ## Part B: the quotient Sobolev space `H¹(0,ℓ) ⧸ N` -/

namespace RobinCaps.Sobolev

variable {ℓ : ℝ}

/-! ### The null subspace and the quotient -/

/-- **The subspace of `H¹` elements vanishing on `[[0,ℓ]]`** (the unordered closed interval
`uIcc 0 ℓ`, which is `Icc 0 ℓ` for `ℓ ≥ 0`; see `mem_nullOff_of_nonneg`).  The Robin form and
the mass only see values on `[0,ℓ]`, so both descend to the quotient by this subspace. -/
def nullOff (ℓ : ℝ) : Submodule ℝ (H1 ℓ) where
  carrier := {u | ∀ x ∈ uIcc (0 : ℝ) ℓ, u.toFun x = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := by
    intro u v hu hv x hx
    change u.toFun x + v.toFun x = 0
    rw [hu x hx, hv x hx, add_zero]
  smul_mem' := by
    intro c u hu x hx
    change c * u.toFun x = 0
    rw [hu x hx, mul_zero]

theorem mem_nullOff {u : H1 ℓ} :
    u ∈ nullOff ℓ ↔ ∀ x ∈ uIcc (0 : ℝ) ℓ, u.toFun x = 0 := Iff.rfl

/-- For `ℓ ≥ 0`, membership in `nullOff ℓ` is vanishing on `Icc 0 ℓ`. -/
theorem mem_nullOff_of_nonneg (hℓ : 0 ≤ ℓ) {u : H1 ℓ} :
    u ∈ nullOff ℓ ↔ ∀ x ∈ Icc (0 : ℝ) ℓ, u.toFun x = 0 := by
  rw [mem_nullOff, uIcc_of_le hℓ]

/-- **The quotient Sobolev space** `H1Q ℓ = H1 ℓ ⧸ nullOff ℓ`. -/
abbrev H1Q (ℓ : ℝ) := H1 ℓ ⧸ nullOff ℓ

/-- The derivative of an element of `nullOff ℓ` vanishes in the interior of `[[0,ℓ]]`
(the function is locally constant there). -/
theorem deriv_eq_zero_of_mem_nullOff {u : H1 ℓ} (hu : u ∈ nullOff ℓ) {x : ℝ}
    (hx : x ∈ Ioo (0 ⊓ ℓ) (0 ⊔ ℓ)) : deriv u.toFun x = 0 := by
  have hev : u.toFun =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact hu y (Ioo_subset_Icc_self hy)
  rw [hev.deriv_eq, deriv_const]

/-- The Robin bilinear form vanishes when its first argument is in `nullOff ℓ`. -/
theorem robinBilin_eq_zero_of_mem_nullOff (p q : ℝ) {u : H1 ℓ} (hu : u ∈ nullOff ℓ)
    (v : H1 ℓ) : robinBilin p q ℓ u v = 0 := by
  have h0 : u.toFun 0 = 0 := hu 0 left_mem_uIcc
  have hl : u.toFun ℓ = 0 := hu ℓ right_mem_uIcc
  have hae : ∀ᵐ x : ℝ, x ≠ 0 ⊔ ℓ := by
    rw [ae_iff]
    simp
  have hint : (∫ x in (0 : ℝ)..ℓ, deriv u.toFun x * deriv v.toFun x)
      = ∫ x in (0 : ℝ)..ℓ, (0 : ℝ) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hae] with x hx hmem
    have hmem' : x ∈ Ioc (0 ⊓ ℓ) (0 ⊔ ℓ) := hmem
    have hx' : x ∈ Ioo (0 ⊓ ℓ) (0 ⊔ ℓ) := ⟨hmem'.1, lt_of_le_of_ne hmem'.2 hx⟩
    rw [deriv_eq_zero_of_mem_nullOff hu hx', zero_mul]
  unfold robinBilin
  rw [hint, intervalIntegral.integral_zero, h0, hl]
  ring

/-- The mass bilinear form vanishes when its first argument is in `nullOff ℓ`. -/
theorem massBilin_eq_zero_of_mem_nullOff {u : H1 ℓ} (hu : u ∈ nullOff ℓ) (v : H1 ℓ) :
    massBilin ℓ u v = 0 := by
  unfold massBilin
  have h : (∫ x in (0 : ℝ)..ℓ, u.toFun x * v.toFun x) = ∫ x in (0 : ℝ)..ℓ, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [hu x hx, zero_mul]
  rw [h, intervalIntegral.integral_zero]

/-- The mass vanishes on `nullOff ℓ`. -/
theorem mass_eq_zero_of_mem_nullOff {u : H1 ℓ} (hu : u ∈ nullOff ℓ) : mass ℓ u = 0 := by
  rw [← massBilin_self]
  exact massBilin_eq_zero_of_mem_nullOff hu u

/-! ### The bilinear forms as bundled bilinear maps, and their descent -/

/-- The Robin bilinear form as a bundled bilinear map. -/
def robinBilinₗ (p q ℓ : ℝ) : H1 ℓ →ₗ[ℝ] H1 ℓ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (robinBilin p q ℓ) (robinBilin_add_left p q ℓ)
    (fun c u v => (robinBilin_smul_left p q ℓ c u v).trans (smul_eq_mul c _).symm)
    (robinBilin_add_right p q ℓ)
    (fun c u v => (robinBilin_smul_right p q ℓ c u v).trans (smul_eq_mul c _).symm)

@[simp] theorem robinBilinₗ_apply (p q ℓ : ℝ) (u v : H1 ℓ) :
    robinBilinₗ p q ℓ u v = robinBilin p q ℓ u v := rfl

/-- The mass bilinear form as a bundled bilinear map. -/
def massBilinₗ (ℓ : ℝ) : H1 ℓ →ₗ[ℝ] H1 ℓ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (massBilin ℓ) (massBilin_add_left ℓ)
    (fun c u v => (massBilin_smul_left ℓ c u v).trans (smul_eq_mul c _).symm)
    (massBilin_add_right ℓ)
    (fun c u v => (massBilin_smul_right ℓ c u v).trans (smul_eq_mul c _).symm)

@[simp] theorem massBilinₗ_apply (ℓ : ℝ) (u v : H1 ℓ) :
    massBilinₗ ℓ u v = massBilin ℓ u v := rfl

/-- **Descent of a bilinear form to a quotient.**  A bilinear map `Bl : M →ₗ M →ₗ ℝ`
vanishing whenever either argument lies in `N` descends to `M ⧸ N` in both arguments. -/
def descendBilin {M : Type*} [AddCommGroup M] [Module ℝ M] (N : Submodule ℝ M)
    (Bl : M →ₗ[ℝ] M →ₗ[ℝ] ℝ) (hl : ∀ u ∈ N, ∀ v, Bl u v = 0)
    (hr : ∀ u, ∀ v ∈ N, Bl u v = 0) : (M ⧸ N) →ₗ[ℝ] (M ⧸ N) →ₗ[ℝ] ℝ :=
  (N.liftQ (N.liftQ Bl (fun u hu => LinearMap.mem_ker.mpr
      (LinearMap.ext fun v => (hl u hu v).trans (LinearMap.zero_apply v).symm))).flip
    (fun v hv => LinearMap.mem_ker.mpr (LinearMap.ext fun x =>
      Submodule.Quotient.induction_on N x (fun u =>
        (hr u v hv).trans (LinearMap.zero_apply _).symm)))).flip

@[simp] theorem descendBilin_mk {M : Type*} [AddCommGroup M] [Module ℝ M]
    (N : Submodule ℝ M) (Bl : M →ₗ[ℝ] M →ₗ[ℝ] ℝ) (hl : ∀ u ∈ N, ∀ v, Bl u v = 0)
    (hr : ∀ u, ∀ v ∈ N, Bl u v = 0) (u v : M) :
    descendBilin N Bl hl hr (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) = Bl u v := rfl

/-- **The Robin bilinear form on the quotient `H1Q ℓ`.** -/
def robinBilinQ (p q ℓ : ℝ) : H1Q ℓ →ₗ[ℝ] H1Q ℓ →ₗ[ℝ] ℝ :=
  descendBilin (nullOff ℓ) (robinBilinₗ p q ℓ)
    (fun u hu v => robinBilin_eq_zero_of_mem_nullOff p q hu v)
    (fun u v hv => by
      rw [robinBilinₗ_apply, robinBilin_comm]
      exact robinBilin_eq_zero_of_mem_nullOff p q hv u)

@[simp] theorem robinBilinQ_mk (p q ℓ : ℝ) (u v : H1 ℓ) :
    robinBilinQ p q ℓ (Submodule.Quotient.mk u) (Submodule.Quotient.mk v)
      = robinBilin p q ℓ u v := rfl

/-- **The mass bilinear form on the quotient `H1Q ℓ`.** -/
def massBilinQ (ℓ : ℝ) : H1Q ℓ →ₗ[ℝ] H1Q ℓ →ₗ[ℝ] ℝ :=
  descendBilin (nullOff ℓ) (massBilinₗ ℓ)
    (fun u hu v => massBilin_eq_zero_of_mem_nullOff hu v)
    (fun u v hv => by
      rw [massBilinₗ_apply, massBilin_comm]
      exact massBilin_eq_zero_of_mem_nullOff hv u)

@[simp] theorem massBilinQ_mk (ℓ : ℝ) (u v : H1 ℓ) :
    massBilinQ ℓ (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) = massBilin ℓ u v := rfl

/-- **The Robin quadratic form on the quotient.** -/
def robinFormQ (p q ℓ : ℝ) (w : H1Q ℓ) : ℝ := robinBilinQ p q ℓ w w

/-- **The mass on the quotient.** -/
def massQ (ℓ : ℝ) (w : H1Q ℓ) : ℝ := massBilinQ ℓ w w

@[simp] theorem robinFormQ_mk (p q ℓ : ℝ) (u : H1 ℓ) :
    robinFormQ p q ℓ (Submodule.Quotient.mk u) = robinForm p q ℓ u := by
  rw [robinFormQ, robinBilinQ_mk, robinBilin_self]

@[simp] theorem massQ_mk (ℓ : ℝ) (u : H1 ℓ) :
    massQ ℓ (Submodule.Quotient.mk u) = mass ℓ u := by
  rw [massQ, massBilinQ_mk, massBilin_self]

/-- **The min–max values of the Robin form on the quotient space.** -/
def robinMinmaxQ (p q ℓ : ℝ) (j : ℕ) : ℝ :=
  Spectrum.minmax (robinFormQ p q ℓ) (massQ ℓ) j

/-! ### Positivity and nonnegativity on the quotient -/

/-- An `H¹` element of zero mass vanishes on `[0,ℓ]` (continuity). -/
theorem mem_nullOff_of_mass_eq_zero (hℓ : 0 < ℓ) {u : H1 ℓ} (hm : mass ℓ u = 0) :
    u ∈ nullOff ℓ := by
  rw [mem_nullOff_of_nonneg hℓ.le]
  intro x hx
  by_contra hne
  have hcont : ContinuousOn (fun y => u.toFun y ^ 2) (Icc (0 : ℝ) ℓ) := by
    have h := u.ac.continuousOn.pow 2
    rwa [uIcc_of_le hℓ.le] at h
  have hpos : 0 < ∫ y in (0 : ℝ)..ℓ, u.toFun y ^ 2 :=
    intervalIntegral.integral_pos hℓ hcont (fun y _ => sq_nonneg _)
      ⟨x, hx, lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))⟩
  have hpos' : 0 < mass ℓ u := hpos
  exact absurd hm (ne_of_gt hpos')

theorem massQ_nonneg (hℓ : 0 ≤ ℓ) (w : H1Q ℓ) : 0 ≤ massQ ℓ w := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective (nullOff ℓ) w
  rw [massQ_mk]
  exact mass_nonneg ℓ u hℓ

/-- **The mass is positive definite on the quotient** (for `ℓ > 0`). -/
theorem massQ_pos (hℓ : 0 < ℓ) (w : H1Q ℓ) (hw : w ≠ 0) : 0 < massQ ℓ w := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective (nullOff ℓ) w
  rw [massQ_mk]
  rcases (mass_nonneg ℓ u hℓ.le).lt_or_eq with h | h
  · exact h
  · exact absurd ((Submodule.Quotient.mk_eq_zero (nullOff ℓ)).mpr
      (mem_nullOff_of_mass_eq_zero hℓ h.symm)) hw

/-- Nonnegativity of the Robin form for nonnegative parameters. -/
theorem robinForm_nonneg (p q ℓ : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hℓ : 0 ≤ ℓ) (u : H1 ℓ) :
    0 ≤ robinForm p q ℓ u := by
  unfold robinForm
  have hd := dirichlet_nonneg ℓ u hℓ
  have h0 : 0 ≤ p * u.toFun 0 ^ 2 := mul_nonneg hp (sq_nonneg _)
  have h1 : 0 ≤ q * u.toFun ℓ ^ 2 := mul_nonneg hq (sq_nonneg _)
  linarith

theorem robinFormQ_nonneg (p q ℓ : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hℓ : 0 ≤ ℓ) (w : H1Q ℓ) :
    0 ≤ robinFormQ p q ℓ w := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective (nullOff ℓ) w
  rw [robinFormQ_mk]
  exact robinForm_nonneg p q ℓ hp hq hℓ u

/-- The lower ratio bound of the engine holds on the quotient (with constant `0`). -/
theorem bddBelowRatio_robinFormQ (p q ℓ : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hℓ : 0 ≤ ℓ) :
    Spectrum.BddBelowRatio (robinFormQ p q ℓ) (massQ ℓ) :=
  ⟨0, le_rfl, fun w _ => div_nonneg (robinFormQ_nonneg p q ℓ hp hq hℓ w) (massQ_nonneg hℓ w)⟩

/-! ### Diagonal expansion of a bilinear form on an orthogonal family -/

/-- If `f` is orthogonal for the bilinear map `Bl` with diagonal `d`, then
`Bl (Σ cᵢ fᵢ) (Σ cᵢ fᵢ) = Σ cᵢ² dᵢ`. -/
theorem bilin_sum_diag {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Type*} [AddCommGroup M]
    [Module ℝ M] (Bl : M →ₗ[ℝ] M →ₗ[ℝ] ℝ) (f : ι → M) (d : ι → ℝ)
    (hoff : ∀ i k, i ≠ k → Bl (f i) (f k) = 0) (hdiag : ∀ i, Bl (f i) (f i) = d i)
    (c : ι → ℝ) :
    Bl (∑ i, c i • f i) (∑ i, c i • f i) = ∑ i, c i ^ 2 * d i := by
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · rw [hdiag]; ring
  · intro k _ hk
    rw [hoff k i hk, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-! ### Monotonicity of `μ` in the index (non-strict form) -/

theorem mu_le_mu (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ)
    {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) (hij : i ≤ j) :
    Interval.mu p q ℓ i hp hq hℓ hi ≤ Interval.mu p q ℓ j hp hq hℓ hj := by
  rcases hij.lt_or_eq with h | h
  · exact (mu_lt_mu p q ℓ hp hq hℓ hi hj h).le
  · subst h
    exact le_rfl

/-! ### The trial space spanned by the first `j` eigenfunctions -/

/-- The first `j` phase eigenfunctions, indexed by `Fin j` (`i ↦ f_{i+1}`). -/
def eigFamily (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) (j : ℕ) : Fin j → H1 ℓ :=
  fun i => phaseEigenH1 p q ℓ (i.1 + 1) hp hq hℓ (Nat.le_add_left 1 i.1)

theorem eigFamily_massBilin_eq_zero (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ)
    (j : ℕ) {i k : Fin j} (hik : i ≠ k) :
    massBilin ℓ (eigFamily p q ℓ hp hq hℓ j i) (eigFamily p q ℓ hp hq hℓ j k) = 0 :=
  phaseEigen_massBilin_eq_zero p q ℓ _ _ hp hq hℓ
    (fun h => hik (Fin.ext (by omega)))

theorem eigFamily_robinBilin_eq_zero (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ)
    (j : ℕ) {i k : Fin j} (hik : i ≠ k) :
    robinBilin p q ℓ (eigFamily p q ℓ hp hq hℓ j i) (eigFamily p q ℓ hp hq hℓ j k) = 0 :=
  phaseEigen_robinBilin_eq_zero p q ℓ _ _ hp hq hℓ
    (fun h => hik (Fin.ext (by omega)))

theorem eigFamily_mass_pos (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ)
    (j : ℕ) (i : Fin j) : 0 < mass ℓ (eigFamily p q ℓ hp hq hℓ j i) :=
  phaseEigen_mass_pos p q ℓ _ hp hq hℓ

/-- The mass of a linear combination of the first `j` eigenfunctions. -/
theorem eigFamily_mass_sum (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ)
    (j : ℕ) (c : Fin j → ℝ) :
    mass ℓ (∑ i, c i • eigFamily p q ℓ hp hq hℓ j i)
      = ∑ i, c i ^ 2 * mass ℓ (eigFamily p q ℓ hp hq hℓ j i) := by
  rw [← massBilin_self, ← massBilinₗ_apply]
  exact bilin_sum_diag (massBilinₗ ℓ) (eigFamily p q ℓ hp hq hℓ j)
    (fun i => mass ℓ (eigFamily p q ℓ hp hq hℓ j i))
    (fun i k hik => eigFamily_massBilin_eq_zero p q ℓ hp hq hℓ j hik)
    (fun i => massBilin_self ℓ _) c

/-- The Robin form of a linear combination of the first `j` eigenfunctions. -/
theorem eigFamily_robinForm_sum (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ)
    (j : ℕ) (c : Fin j → ℝ) :
    robinForm p q ℓ (∑ i, c i • eigFamily p q ℓ hp hq hℓ j i)
      = ∑ i, c i ^ 2 * (Interval.mu p q ℓ (i.1 + 1) hp hq hℓ (Nat.le_add_left 1 i.1)
          * mass ℓ (eigFamily p q ℓ hp hq hℓ j i)) := by
  rw [← robinBilin_self, ← robinBilinₗ_apply]
  exact bilin_sum_diag (robinBilinₗ p q ℓ) (eigFamily p q ℓ hp hq hℓ j)
    (fun i => Interval.mu p q ℓ (i.1 + 1) hp hq hℓ (Nat.le_add_left 1 i.1)
      * mass ℓ (eigFamily p q ℓ hp hq hℓ j i))
    (fun i k hik => eigFamily_robinBilin_eq_zero p q ℓ hp hq hℓ j hik)
    (fun i => by
      beta_reduce
      rw [robinBilinₗ_apply, ← massBilin_self]
      exact phaseEigen_robinBilin_eq p q ℓ _ _ hp hq hℓ) c

/-- The first `j` eigenfunctions are linearly independent (Gram argument with the mass). -/
theorem eigFamily_linearIndependent (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ)
    (j : ℕ) : LinearIndependent ℝ (eigFamily p q ℓ hp hq hℓ j) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hm0 : mass ℓ (0 : H1 ℓ) = 0 := by simp [mass]
  have hm : mass ℓ (∑ i, g i • eigFamily p q ℓ hp hq hℓ j i) = 0 := by rw [hg, hm0]
  rw [eigFamily_mass_sum] at hm
  have hnn : ∀ k ∈ Finset.univ, 0 ≤ g k ^ 2 * mass ℓ (eigFamily p q ℓ hp hq hℓ j k) :=
    fun k _ => mul_nonneg (sq_nonneg _) (eigFamily_mass_pos p q ℓ hp hq hℓ j k).le
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hm i (Finset.mem_univ i)
  rcases mul_eq_zero.mp hzero with h | h
  · exact (pow_eq_zero_iff two_ne_zero).mp h
  · exact absurd h (ne_of_gt (eigFamily_mass_pos p q ℓ hp hq hℓ j i))

/-- The span of the first `j` eigenfunctions in `H1 ℓ`. -/
def eigSpan (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) (j : ℕ) : Submodule ℝ (H1 ℓ) :=
  Submodule.span ℝ (Set.range (eigFamily p q ℓ hp hq hℓ j))

theorem eigSpan_finrank (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) (j : ℕ) :
    Module.finrank ℝ (eigSpan p q ℓ hp hq hℓ j) = j := by
  rw [eigSpan, finrank_span_eq_card (eigFamily_linearIndependent p q ℓ hp hq hℓ j),
    Fintype.card_fin]

/-- A nonzero element of the span has positive mass. -/
theorem eigSpan_mass_pos (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) (j : ℕ)
    {u : H1 ℓ} (hu : u ∈ eigSpan p q ℓ hp hq hℓ j) (hne : u ≠ 0) : 0 < mass ℓ u := by
  rw [eigSpan, Submodule.mem_span_range_iff_exists_fun] at hu
  obtain ⟨c, rfl⟩ := hu
  rw [eigFamily_mass_sum]
  have hc : ∃ i, c i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    simp [h]
  obtain ⟨i, hi⟩ := hc
  have hnn : ∀ k ∈ Finset.univ, 0 ≤ c k ^ 2 * mass ℓ (eigFamily p q ℓ hp hq hℓ j k) :=
    fun k _ => mul_nonneg (sq_nonneg _) (eigFamily_mass_pos p q ℓ hp hq hℓ j k).le
  have hpos : 0 < c i ^ 2 * mass ℓ (eigFamily p q ℓ hp hq hℓ j i) :=
    mul_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi)))
      (eigFamily_mass_pos p q ℓ hp hq hℓ j i)
  exact lt_of_lt_of_le hpos (Finset.single_le_sum hnn (Finset.mem_univ i))

/-- **The `j`-dimensional trial space in the quotient**: the image of `eigSpan`. -/
def trialSpaceQ (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) (j : ℕ) :
    Submodule ℝ (H1Q ℓ) :=
  LinearMap.range ((nullOff ℓ).mkQ.comp (eigSpan p q ℓ hp hq hℓ j).subtype)

/-- The quotient map is injective on the span (nonzero combinations have positive mass,
hence do not vanish on `[0,ℓ]`), so the trial space is `j`-dimensional. -/
theorem trialSpaceQ_finrank (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) (j : ℕ) :
    Module.finrank ℝ (trialSpaceQ p q ℓ hp hq hℓ j) = j := by
  have hinj : Function.Injective
      ((nullOff ℓ).mkQ.comp (eigSpan p q ℓ hp hq hℓ j).subtype) := by
    intro s t hst
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Submodule.mkQ_apply] at hst
    rw [Submodule.Quotient.eq] at hst
    have hmem : ((s : H1 ℓ) - t) ∈ eigSpan p q ℓ hp hq hℓ j := sub_mem s.2 t.2
    by_contra hne
    have hne' : (s : H1 ℓ) - t ≠ 0 := sub_ne_zero.mpr (fun h => hne (Subtype.ext h))
    exact absurd (mass_eq_zero_of_mem_nullOff hst)
      (ne_of_gt (eigSpan_mass_pos p q ℓ hp hq hℓ j hmem hne'))
  rw [trialSpaceQ, LinearMap.finrank_range_of_inj hinj, eigSpan_finrank]

/-- **The trial inequality** `robinFormQ ≤ μ_j · massQ` on the trial space. -/
theorem trialSpaceQ_le (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) (j : ℕ)
    (hj : 1 ≤ j) :
    ∀ w ∈ trialSpaceQ p q ℓ hp hq hℓ j, w ≠ 0 →
      robinFormQ p q ℓ w ≤ Interval.mu p q ℓ j hp hq hℓ hj * massQ ℓ w := by
  intro w hw _
  obtain ⟨s, rfl⟩ := LinearMap.mem_range.mp hw
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, Submodule.mkQ_apply]
  rw [robinFormQ_mk, massQ_mk]
  have hs : (s : H1 ℓ) ∈ Submodule.span ℝ (Set.range (eigFamily p q ℓ hp hq hℓ j)) := s.2
  rw [Submodule.mem_span_range_iff_exists_fun] at hs
  obtain ⟨c, hc⟩ := hs
  rw [← hc, eigFamily_robinForm_sum, eigFamily_mass_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hmu : Interval.mu p q ℓ (i.1 + 1) hp hq hℓ (Nat.le_add_left 1 i.1)
      ≤ Interval.mu p q ℓ j hp hq hℓ hj :=
    mu_le_mu p q ℓ hp hq hℓ _ hj (by omega)
  have hm : 0 ≤ mass ℓ (eigFamily p q ℓ hp hq hℓ j i) :=
    (eigFamily_mass_pos p q ℓ hp hq hℓ j i).le
  calc c i ^ 2 * (Interval.mu p q ℓ (i.1 + 1) hp hq hℓ (Nat.le_add_left 1 i.1)
          * mass ℓ (eigFamily p q ℓ hp hq hℓ j i))
      ≤ c i ^ 2 * (Interval.mu p q ℓ j hp hq hℓ hj * mass ℓ (eigFamily p q ℓ hp hq hℓ j i)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmu hm) (sq_nonneg _)
    _ = Interval.mu p q ℓ j hp hq hℓ hj * (c i ^ 2 * mass ℓ (eigFamily p q ℓ hp hq hℓ j i)) := by
        ring

/-! ### The upper half `λ_j ≤ μ_j` for every `j ≥ 1` -/

/-- **The upper half of the variation bridge on the quotient space**: for all `j ≥ 1`,
`robinMinmaxQ p q ℓ j ≤ μ_j(p,q;ℓ)`. -/
theorem robinMinmaxQ_le_mu (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) (j : ℕ)
    (hj : 1 ≤ j) : robinMinmaxQ p q ℓ j ≤ Interval.mu p q ℓ j hp hq hℓ hj :=
  Spectrum.minmax_le_of_trial' (robinFormQ p q ℓ) (massQ ℓ) j hj (massQ_pos hℓ)
    (bddBelowRatio_robinFormQ p q ℓ hp.le hq.le hℓ.le) (trialSpaceQ p q ℓ hp hq hℓ j)
    (trialSpaceQ_finrank p q ℓ hp hq hℓ j) _ (trialSpaceQ_le p q ℓ hp hq hℓ j hj)

/-! ### The lower half, conditional on a Picone-type inequality -/

/-- **Lower bound wrapper.**  Given a constraint functional `φ` on `H1 ℓ` vanishing on
`nullOff ℓ` with `(j-1)`-dimensional range, and the Picone-type inequality
`μ_j · mass u ≤ robinForm u` on `ker φ`, we get `μ_j ≤ robinMinmaxQ p q ℓ j`. -/
theorem mu_le_robinMinmaxQ_of_picone (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ)
    (j : ℕ) (hj : 1 ≤ j) (φ : H1 ℓ →ₗ[ℝ] (Fin (j - 1) → ℝ))
    (hφ₀ : ∀ u ∈ nullOff ℓ, φ u = 0)
    (hφ : Module.finrank ℝ (LinearMap.range φ) = j - 1)
    (hP : ∀ u : H1 ℓ, φ u = 0 →
      Interval.mu p q ℓ j hp hq hℓ hj * mass ℓ u ≤ robinForm p q ℓ u) :
    Interval.mu p q ℓ j hp hq hℓ hj ≤ robinMinmaxQ p q ℓ j := by
  have hker : nullOff ℓ ≤ LinearMap.ker φ := fun u hu => LinearMap.mem_ker.mpr (hφ₀ u hu)
  let φQ : H1Q ℓ →ₗ[ℝ] (Fin (j - 1) → ℝ) := (nullOff ℓ).liftQ φ hker
  have hφQ : Module.finrank ℝ (LinearMap.range φQ) = j - 1 := by
    rw [show LinearMap.range φQ = LinearMap.range φ from
      Submodule.range_liftQ (nullOff ℓ) φ hker]
    exact hφ
  refine Spectrum.le_minmax_of_codim' (robinFormQ p q ℓ) (massQ ℓ) j hj (massQ_pos hℓ) ?_
    φQ hφQ _ ?_ ⟨trialSpaceQ p q ℓ hp hq hℓ j, trialSpaceQ_finrank p q ℓ hp hq hℓ j⟩
  · intro V hV
    haveI : FiniteDimensional ℝ V := FiniteDimensional.of_finrank_pos (by omega)
    exact Spectrum.bddAbove_ratio_of_bilinear (robinBilinQ p q ℓ) (massBilinQ ℓ)
      (massQ_pos hℓ) V
  · intro w _ hw
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective (nullOff ℓ) w
    rw [robinFormQ_mk, massQ_mk]
    exact hP u hw

/-- **Point evaluation** `u ↦ u.toFun x` as a linear functional on `H1 ℓ`. -/
def evalAt (ℓ x : ℝ) : H1 ℓ →ₗ[ℝ] ℝ where
  toFun u := u.toFun x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem evalAt_apply (ℓ x : ℝ) (u : H1 ℓ) : evalAt ℓ x u = u.toFun x := rfl

/-- Point evaluation at `x ∈ [[0,ℓ]]` vanishes on `nullOff ℓ`, hence descends to `H1Q ℓ`. -/
theorem evalAt_eq_zero_of_mem_nullOff {x : ℝ} (hx : x ∈ uIcc (0 : ℝ) ℓ) {u : H1 ℓ}
    (hu : u ∈ nullOff ℓ) : evalAt ℓ x u = 0 := hu x hx

/-- Point evaluation descended to the quotient. -/
def evalAtQ (ℓ : ℝ) {x : ℝ} (hx : x ∈ uIcc (0 : ℝ) ℓ) : H1Q ℓ →ₗ[ℝ] ℝ :=
  (nullOff ℓ).liftQ (evalAt ℓ x)
    (fun _ hu => LinearMap.mem_ker.mpr (evalAt_eq_zero_of_mem_nullOff hx hu))

@[simp] theorem evalAtQ_mk (ℓ : ℝ) {x : ℝ} (hx : x ∈ uIcc (0 : ℝ) ℓ) (u : H1 ℓ) :
    evalAtQ ℓ hx (Submodule.Quotient.mk u) = u.toFun x := rfl

/-- The constant function `c` as an element of `H1 ℓ`. -/
def H1.const (ℓ c : ℝ) : H1 ℓ where
  toFun := fun _ => c
  ac := by
    have h : LipschitzOnWith 0 (fun _ : ℝ => c) (uIcc (0 : ℝ) ℓ) :=
      (LipschitzWith.const c).lipschitzOnWith
    exact h.absolutelyContinuousOnInterval
  deriv_int := by
    have h : (fun x => deriv (fun _ : ℝ => c) x) = fun _ => (0 : ℝ) := by
      funext x; exact deriv_const x c
    rw [h]
    exact intervalIntegrable_const
  deriv_sq_int := by
    have h : (fun x => deriv (fun _ : ℝ => c) x ^ 2) = fun _ => (0 : ℝ) := by
      funext x; rw [deriv_const]; ring
    rw [h]
    exact intervalIntegrable_const
  ftc := by
    intro x _
    simp

@[simp] theorem H1.const_toFun (ℓ c : ℝ) : (H1.const ℓ c).toFun = fun _ => c := rfl

/-- **The `j = 1` lower bound**: `μ₁ ≤ robinMinmaxQ p q ℓ 1` given the Picone inequality
`μ₁ · mass u ≤ robinForm u` for all `u`. -/
theorem mu_le_robinMinmaxQ_one_of_picone (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ)
    (hP : ∀ u : H1 ℓ,
      Interval.mu p q ℓ 1 hp hq hℓ (le_refl 1) * mass ℓ u ≤ robinForm p q ℓ u) :
    Interval.mu p q ℓ 1 hp hq hℓ (le_refl 1) ≤ robinMinmaxQ p q ℓ 1 := by
  refine mu_le_robinMinmaxQ_of_picone p q ℓ hp hq hℓ 1 (le_refl 1)
    (0 : H1 ℓ →ₗ[ℝ] (Fin (1 - 1) → ℝ)) (fun _ _ => rfl) ?_ (fun u _ => hP u)
  rw [LinearMap.range_zero, finrank_bot]

/-- **The `j = 2` lower bound**: `μ₂ ≤ robinMinmaxQ p q ℓ 2` given the Picone inequality
`μ₂ · mass u ≤ robinForm u` for all `u` vanishing at a point `x₁ ∈ [0,ℓ]` (the node of the
second eigenfunction). -/
theorem mu_le_robinMinmaxQ_two_of_picone (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ)
    {x₁ : ℝ} (hx₁ : x₁ ∈ Icc (0 : ℝ) ℓ)
    (hP : ∀ u : H1 ℓ, u.toFun x₁ = 0 →
      Interval.mu p q ℓ 2 hp hq hℓ (by norm_num) * mass ℓ u ≤ robinForm p q ℓ u) :
    Interval.mu p q ℓ 2 hp hq hℓ (by norm_num) ≤ robinMinmaxQ p q ℓ 2 := by
  have hx₁' : x₁ ∈ uIcc (0 : ℝ) ℓ := by rw [uIcc_of_le hℓ.le]; exact hx₁
  let φ : H1 ℓ →ₗ[ℝ] (Fin 1 → ℝ) := LinearMap.pi fun _ => evalAt ℓ x₁
  have hφ₀ : ∀ u ∈ nullOff ℓ, φ u = 0 := by
    intro u hu
    funext i
    exact evalAt_eq_zero_of_mem_nullOff hx₁' hu
  have hsurj : Function.Surjective φ := by
    intro v
    refine ⟨v 0 • H1.const ℓ 1, ?_⟩
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    simp [φ, hi]
  have hφ : Module.finrank ℝ (LinearMap.range φ) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fin_fun]
  exact mu_le_robinMinmaxQ_of_picone p q ℓ hp hq hℓ 2 (by norm_num) φ hφ₀ hφ
    (fun u hu => hP u (congrFun hu 0))

end RobinCaps.Sobolev
