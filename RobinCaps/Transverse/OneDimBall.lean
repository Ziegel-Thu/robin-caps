import RobinCaps.Interval.Gap

/-!
# The transverse problem in dimension `m = 1`

Formalizes the `m = 1` case of the transverse estimates of Lemma 4.1
(`lem:transverse`) of `reference/robin_endcaps_corrected_en.tex` (line 439).

In transverse dimension `m = 1` (planar thin domains, `n = 2`) the transverse
ball `B_1(R)` is the interval `(-R, R)`, and the transverse Robin eigenvalue
problem

  `-ψ'' = ν ψ` on `(-R, R)`,  `±ψ'(±R) + α ψ(±R) = 0`

is exactly the symmetric interval Robin problem with `p = q = α` and length
`ℓ = 2R` already formalized in `RobinCaps.Interval.Phase` and
`RobinCaps.Interval.Gap`.  Hence

* `ν_R = λ₁(B_1(R); α) = mu α α (2R) 1`,
* `λ₂(B_1(R); α) = mu α α (2R) 2`,

and by `RobinCaps.Sobolev.Variational` these `mu`'s are the genuine variational
(min–max) Robin eigenvalues.

The results proved here are, for `m = 1`:

* `nuR_expansion`  : `eq:nu-expansion`, `R² ν_R = mαR + O(R²) = αR + O(R²)`;
* `transverse_gap_oneDim` : `eq:transverse-gap`, `λ₂(B_1(R);α) - ν_R ≥ c R⁻²`.

Both rest on `muSym_one_expansion`, the small-`β` expansion
`μ₁(β, β, 1) = 2β + O(β²)` of the first symmetric interval eigenvalue, which is
extracted directly from the phase equation `k = 2 arctan(β/k)`.

The `H¹` statements `eq:Psi-H1` and `eq:d-R` are *not* proved here; the final
section records them as explicit `Prop`-valued targets `PsiH1Target` and
`dRTarget`, phrased for `m = 1` on the explicit phase-equation ground state.
-/

open Set Filter
open scoped Topology

namespace RobinCaps.Transverse

noncomputable section

/-! ### Two elementary `arctan` bounds

`arctan x ≤ x` and `x - x³/3 ≤ arctan x` for `x ≥ 0`.  Both follow from
monotonicity of an explicit primitive whose derivative is manifestly
nonnegative. -/

/-- `arctan x ≤ x` for `x ≥ 0`. -/
theorem arctan_le_self {x : ℝ} (hx : 0 ≤ x) : Real.arctan x ≤ x := by
  have hmono : Monotone fun t : ℝ => t - Real.arctan t := by
    refine monotone_of_deriv_nonneg ?_ ?_
    · exact differentiable_id.sub Real.differentiable_arctan
    · intro t
      have hd : HasDerivAt (fun t : ℝ => t - Real.arctan t) (1 - 1 / (1 + t ^ 2)) t :=
        (hasDerivAt_id t).sub (Real.hasDerivAt_arctan t)
      rw [hd.deriv]
      have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
      rw [sub_nonneg, div_le_one hpos]
      nlinarith [sq_nonneg t]
  have h : (0 : ℝ) - Real.arctan 0 ≤ x - Real.arctan x := hmono hx
  rw [Real.arctan_zero] at h
  linarith

/-- `x - x³/3 ≤ arctan x` for `x ≥ 0`. -/
theorem sub_cube_le_arctan {x : ℝ} (hx : 0 ≤ x) : x - x ^ 3 / 3 ≤ Real.arctan x := by
  have hcube : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t ^ 3 / 3) (t ^ 2) t := by
    intro t
    have h := (hasDerivAt_pow 3 t).div_const 3
    convert h using 1
    push_cast
    ring
  have hmono : Monotone fun t : ℝ => Real.arctan t - (t - t ^ 3 / 3) := by
    refine monotone_of_deriv_nonneg ?_ ?_
    · refine Real.differentiable_arctan.sub (differentiable_id.sub ?_)
      exact fun t => (hcube t).differentiableAt
    · intro t
      have hd : HasDerivAt (fun t : ℝ => Real.arctan t - (t - t ^ 3 / 3))
          (1 / (1 + t ^ 2) - (1 - t ^ 2)) t :=
        (Real.hasDerivAt_arctan t).sub ((hasDerivAt_id t).sub (hcube t))
      rw [hd.deriv]
      have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
      have hEq : 1 / (1 + t ^ 2) - (1 - t ^ 2) = t ^ 4 / (1 + t ^ 2) := by
        field_simp
        ring
      rw [hEq]
      positivity
  have h : Real.arctan 0 - ((0 : ℝ) - (0 : ℝ) ^ 3 / 3) ≤ Real.arctan x - (x - x ^ 3 / 3) :=
    hmono hx
  rw [Real.arctan_zero] at h
  norm_num at h
  linarith

/-! ### The small-parameter expansion of the first symmetric interval eigenvalue -/

/-- **Small-`β` expansion of the first symmetric interval eigenvalue.**

For the unit interval with Robin parameter `β` at both endpoints,
`μ₁(β, β, 1) = 2β + O(β²)` as `β ↓ 0`.  Explicitly, `|μ₁ - 2β| ≤ (2/3) β²`
for `0 < β < 1/2`.

The proof reads the phase equation `k = 2 arctan(β/k)` (here `ℓ = 1`, `j = 1`)
through the two elementary `arctan` bounds above: `arctan x ≤ x` gives
`k² ≤ 2β`, and `x - x³/3 ≤ arctan x` gives `k² ≥ 2β - (2/3) β³/k²`, which is
bootstrapped using the crude lower bound `k² > β`. -/
theorem muSym_one_expansion :
    ∃ C β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, ∀ hβ : 0 < β, β < β₀ →
      |Interval.mu β β 1 1 hβ hβ one_pos (le_refl 1) - 2 * β| ≤ C * β ^ 2 := by
  refine ⟨2 / 3, 1 / 2, by norm_num, ?_⟩
  intro β hβ hβlt
  set k := Interval.phaseRoot β β 1 1 hβ hβ one_pos (le_refl 1) with hkdef
  have hk : 0 < k := Interval.phaseRoot_pos β β 1 1 hβ hβ one_pos (le_refl 1)
  have hmu : Interval.mu β β 1 1 hβ hβ one_pos (le_refl 1) = k ^ 2 := rfl
  have heq0 : Interval.phaseFun β β 1 1 k = 0 :=
    Interval.phaseRoot_eq β β 1 1 hβ hβ one_pos (le_refl 1)
  simp only [Interval.phaseFun, Nat.cast_one, mul_one, sub_self, zero_mul, sub_zero] at heq0
  have hkeq : k = 2 * Real.arctan (β / k) := by linarith
  have hx : 0 < β / k := div_pos hβ hk
  have hbk : β / k * k = β := by field_simp
  -- Upper bound `k² ≤ 2β` from `arctan x ≤ x`.
  have hub : k ^ 2 ≤ 2 * β := by
    have h1 : Real.arctan (β / k) ≤ β / k := arctan_le_self hx.le
    have h2 : k ≤ 2 * (β / k) := by linarith
    have h3 := mul_le_mul_of_nonneg_right h2 hk.le
    nlinarith [h3, hbk]
  -- Crude lower bound `β < k²`.
  have hklb : β < k ^ 2 := by
    by_contra hcon
    push_neg at hcon
    have hkle : k ≤ β / k := by
      rw [le_div_iff₀ hk]
      nlinarith
    have ha1 : Real.arctan k ≤ Real.arctan (β / k) := Real.arctan_mono hkle
    have ha2 : k - k ^ 3 / 3 ≤ Real.arctan k := sub_cube_le_arctan hk.le
    have h4 : 2 * k - 2 * k ^ 3 / 3 ≤ k := by linarith
    have h5 : 3 ≤ 2 * k ^ 2 := by nlinarith [hk, h4]
    linarith
  -- Sharpened lower bound `k² ≥ 2β - (2/3)β²`.
  have hlb : 2 * β - 2 / 3 * β ^ 2 ≤ k ^ 2 := by
    have ha2 : β / k - (β / k) ^ 3 / 3 ≤ Real.arctan (β / k) := sub_cube_le_arctan hx.le
    have h1 : 2 * (β / k) - 2 * (β / k) ^ 3 / 3 ≤ k := by linarith
    have h2 := mul_le_mul_of_nonneg_right h1 hk.le
    have h3 : (2 * (β / k) - 2 * (β / k) ^ 3 / 3) * k = 2 * β - 2 * β ^ 3 / (3 * k ^ 2) := by
      field_simp
    rw [h3] at h2
    have h4 : 2 * β ^ 3 / (3 * k ^ 2) ≤ 2 / 3 * β ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hklb, hβ, sq_nonneg β]
    nlinarith [h2, h4]
  rw [hmu, abs_le]
  constructor <;> nlinarith [hub, hlb, sq_nonneg β]

/-! ### The transverse eigenvalues in dimension `m = 1` -/

/-- The transverse Robin ground state energy `ν_R = λ₁(B_1(R); α)`.

For `m = 1` the transverse ball is the interval `(-R, R)`, congruent to
`(0, 2R)`, and the Robin ground state energy is the first symmetric interval
eigenvalue with `p = q = α` and length `2R`. -/
def nuR (α R : ℝ) (hα : 0 < α) (hR : 0 < R) : ℝ :=
  Interval.mu α α (2 * R) 1 hα hα (by positivity) (le_refl 1)

/-- The second transverse Robin eigenvalue `λ₂(B_1(R); α)`. -/
def lam2R (α R : ℝ) (hα : 0 < α) (hR : 0 < R) : ℝ :=
  Interval.mu α α (2 * R) 2 hα hα (by positivity) (by norm_num)

theorem nuR_pos (α R : ℝ) (hα : 0 < α) (hR : 0 < R) : 0 < nuR α R hα hR :=
  pow_pos (Interval.phaseRoot_pos α α (2 * R) 1 hα hα (by positivity) (le_refl 1)) 2

theorem nuR_lt_lam2R (α R : ℝ) (hα : 0 < α) (hR : 0 < R) :
    nuR α R hα hR < lam2R α R hα hR := by
  have hL : (0 : ℝ) < 2 * R := by positivity
  have h1 : Interval.phaseRoot α α (2 * R) 1 hα hα hL (le_refl 1) < Real.pi / (2 * R) := by
    have h := Interval.phaseRoot_lt_rightEnd α α (2 * R) 1 hα hα hL (le_refl 1)
    have hre : Interval.rightEnd (2 * R) 1 = Real.pi / (2 * R) := by
      norm_num [Interval.rightEnd]
    rwa [hre] at h
  have h2 : Real.pi / (2 * R) <
      Interval.phaseRoot α α (2 * R) 2 hα hα hL (by norm_num) := by
    have h := Interval.leftEnd_lt_phaseRoot α α (2 * R) 2 hα hα hL (by norm_num)
    have hle : Interval.leftEnd (2 * R) 2 = Real.pi / (2 * R) := by
      norm_num [Interval.leftEnd]
    rwa [hle] at h
  have hpos := Interval.phaseRoot_pos α α (2 * R) 1 hα hα hL (le_refl 1)
  show Interval.phaseRoot α α (2 * R) 1 hα hα hL (le_refl 1) ^ 2 <
    Interval.phaseRoot α α (2 * R) 2 hα hα hL (by norm_num) ^ 2
  nlinarith [h1, h2, hpos]

/-- **`eq:nu-expansion` for `m = 1`**: `R² ν_R = α R + O(R²)` as `R ↓ 0`
(recall `m α R = α R` when `m = 1`). -/
theorem nuR_expansion (α : ℝ) (hα : 0 < α) :
    ∃ C R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, ∀ hR : 0 < R, R < R₀ →
      |R ^ 2 * nuR α R hα hR - α * R| ≤ C * R ^ 2 := by
  obtain ⟨C, β₀, hβ₀, hC⟩ := muSym_one_expansion
  refine ⟨C * α ^ 2, β₀ / (2 * α), by positivity, ?_⟩
  intro R hR hRlt
  have hRne : R ≠ 0 := ne_of_gt hR
  have hL : (0 : ℝ) < 2 * R := by positivity
  have hβ : (0 : ℝ) < 2 * R * α := by positivity
  have hβlt : 2 * R * α < β₀ := by
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * α)] at hRlt
    nlinarith [hRlt]
  have hscal : nuR α R hα hR =
      ((2 * R)⁻¹) ^ 2 * Interval.mu (2 * R * α) (2 * R * α) 1 1 hβ hβ one_pos (le_refl 1) :=
    Interval.mu_scaling α α (2 * R) 1 hα hα hL (le_refl 1)
  set M := Interval.mu (2 * R * α) (2 * R * α) 1 1 hβ hβ one_pos (le_refl 1) with hM
  have hbound : |M - 2 * (2 * R * α)| ≤ C * (2 * R * α) ^ 2 := hC (2 * R * α) hβ hβlt
  have hrw : C * (2 * R * α) ^ 2 = 4 * (C * α ^ 2 * R ^ 2) := by ring
  rw [hrw] at hbound
  have e : R ^ 2 * nuR α R hα hR - α * R = (M - 2 * (2 * R * α)) / 4 := by
    rw [hscal]
    field_simp
    ring
  have habs4 : |(4 : ℝ)| = 4 := by norm_num
  rw [e, abs_div, habs4, div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
  linarith

/-! ### The transverse spectral gap in dimension `m = 1` -/

/-- Scaling law for the symmetric interval gap: `G_β(L) = L⁻² G_{Lβ}(1)`. -/
theorem gap_scaling (L : ℝ) (hL : 0 < L) {β : ℝ} (hβ : 0 < β) :
    Interval.gap L hL β = (L⁻¹) ^ 2 * Interval.gap 1 one_pos (L * β) := by
  have hLβ : 0 < L * β := mul_pos hL hβ
  rw [Interval.gap_eq_mu L hL hβ, Interval.gap_eq_mu 1 one_pos hLβ,
    Interval.mu_scaling β β L 2 hβ hβ hL (by norm_num),
    Interval.mu_scaling β β L 1 hβ hβ hL (le_refl 1)]
  ring

/-- **`eq:transverse-gap` for `m = 1`**: there are `c > 0` and `R₀ > 0` with
`λ₂(B_1(R); α) - ν_R ≥ c R⁻²` for all `0 < R < R₀`.

One may take `c = π²/8`; the proof is the `L = 1` Neumann limit
`G_β(1) → π²` of `RobinCaps.Interval.gap_tendsto` combined with the gap
scaling `G_α(2R) = (2R)⁻² G_{2Rα}(1)`. -/
theorem transverse_gap_oneDim (α : ℝ) (hα : 0 < α) :
    ∃ c R₀ : ℝ, 0 < c ∧ 0 < R₀ ∧ ∀ R : ℝ, ∀ hR : 0 < R, R < R₀ →
      c * R⁻¹ ^ 2 ≤ lam2R α R hα hR - nuR α R hα hR := by
  have hpi : (0 : ℝ) < Real.pi ^ 2 := by positivity
  have htend := Interval.gap_tendsto 1 one_pos
  have hlt : Real.pi ^ 2 / 2 < Real.pi ^ 2 / 1 ^ 2 := by
    have h1 : (Real.pi ^ 2 / 1 ^ 2) = Real.pi ^ 2 := by norm_num
    rw [h1]
    linarith
  have hev : ∀ᶠ β in 𝓝[>] (0 : ℝ), Real.pi ^ 2 / 2 < Interval.gap 1 one_pos β :=
    (tendsto_order.1 htend).1 _ hlt
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  have hupos : (0 : ℝ) < u := hu
  refine ⟨Real.pi ^ 2 / 8, u / (2 * α), by positivity, by positivity, ?_⟩
  intro R hR hRlt
  have hRne : R ≠ 0 := ne_of_gt hR
  have hL : (0 : ℝ) < 2 * R := by positivity
  have hβ : (0 : ℝ) < 2 * R * α := by positivity
  have hβlt : 2 * R * α < u := by
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * α)] at hRlt
    nlinarith [hRlt]
  have hG : Real.pi ^ 2 / 2 < Interval.gap 1 one_pos (2 * R * α) := hsub ⟨hβ, hβlt⟩
  have hkey : Interval.gap (2 * R) hL α =
      ((2 * R)⁻¹) ^ 2 * Interval.gap 1 one_pos (2 * R * α) := gap_scaling (2 * R) hL hα
  have hgap : lam2R α R hα hR - nuR α R hα hR =
      ((2 * R)⁻¹) ^ 2 * Interval.gap 1 one_pos (2 * R * α) := by
    rw [← hkey, Interval.gap_eq_mu (2 * R) hL hα]
    rfl
  have hfac : ((2 * R)⁻¹ : ℝ) ^ 2 = R⁻¹ ^ 2 / 4 := by
    field_simp
    norm_num
  rw [hgap, hfac]
  have hRinv : (0 : ℝ) < R⁻¹ ^ 2 := by positivity
  nlinarith [mul_pos hRinv (sub_pos.mpr hG), hRinv, hG]

/-! ### Targets: the `H¹` statements `eq:Psi-H1` and `eq:d-R` for `m = 1`

These two statements of `lem:transverse` are **not proved** here.  They are
recorded below as `Prop`-valued targets, phrased for `m = 1` on the explicit
ground state supplied by the phase equation, so that a later file can discharge
them without re-deriving the geometry.

For `m = 1` the transverse ball is `B_1(1) = (-1, 1)` and
`ω_1 = |B_1(1)| = 2`, so the constant comparison profile of `eq:Psi-H1` is
`ω_1^{-1/2} = (√2)⁻¹` and the limit in `eq:d-R` is `√ω_1 = √2`. -/

/-- The transverse ground-state profile on `(0, 2R)`:
`x ↦ cos(k x - arctan(α/k))`, where `k` is the first phase root for
`p = q = α`, `ℓ = 2R`.  Up to normalization this is the positive Robin ground
state; indeed `-u'(0) + α u(0) = 0` forces `tan(arctan(α/k)) = α/k`, and the
condition at `x = 2R` is exactly the phase equation. -/
def groundProfile (α R : ℝ) (hα : 0 < α) (hR : 0 < R) (x : ℝ) : ℝ :=
  Real.cos (Interval.phaseRoot α α (2 * R) 1 hα hα (by positivity) (le_refl 1) * x -
    Real.arctan (α / Interval.phaseRoot α α (2 * R) 1 hα hα (by positivity) (le_refl 1)))

/-- The `L²(-1,1)` normalizing factor of the rescaled profile. -/
def scaledNorm (α R : ℝ) (hα : 0 < α) (hR : 0 < R) : ℝ :=
  Real.sqrt (∫ z in (-1 : ℝ)..1, groundProfile α R hα hR (R * (z + 1)) ^ 2)

/-- `Ψ_R` of `eq:scaled-groundstate` for `m = 1`: the `L²`-normalized transverse
ground state transplanted from `B_1(R) = (-R, R)` to `B_1(1) = (-1, 1)`.  The
affine change of variables `z ↦ R (z + 1)` carries `(-1, 1)` onto `(0, 2R)`,
the model of `(-R, R)` used by `RobinCaps.Interval`. -/
def scaledGroundState (α R : ℝ) (hα : 0 < α) (hR : 0 < R) (z : ℝ) : ℝ :=
  groundProfile α R hα hR (R * (z + 1)) / scaledNorm α R hα hR

/-- `d_R` of `eq:d-R` for `m = 1`: `d_R = ∫_{B_1(1)} Ψ_R`. -/
def dR (α R : ℝ) (hα : 0 < α) (hR : 0 < R) : ℝ :=
  ∫ z in (-1 : ℝ)..1, scaledGroundState α R hα hR z

/-- **Target `eq:Psi-H1` for `m = 1`** (open).

`‖Ψ_R - ω_1^{-1/2}‖_{H¹(B_1(1))} ≤ C R` as `R ↓ 0`, written out as a bound on
the squared `H¹` norm with `ω_1^{-1/2} = (√2)⁻¹`. -/
def PsiH1Target (α : ℝ) (hα : 0 < α) : Prop :=
  ∃ C R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, ∀ hR : 0 < R, R < R₀ →
    (∫ z in (-1 : ℝ)..1, (scaledGroundState α R hα hR z - (Real.sqrt 2)⁻¹) ^ 2) +
        (∫ z in (-1 : ℝ)..1, deriv (scaledGroundState α R hα hR) z ^ 2)
      ≤ C ^ 2 * R ^ 2

/-- **Target `eq:d-R` for `m = 1`** (open).

`d_R = √ω_1 + O(R²) = √2 + O(R²)` and `d_R ≥ ½ √ω_1` for small `R`. -/
def dRTarget (α : ℝ) (hα : 0 < α) : Prop :=
  ∃ C R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, ∀ hR : 0 < R, R < R₀ →
    |dR α R hα hR - Real.sqrt 2| ≤ C * R ^ 2 ∧ Real.sqrt 2 / 2 ≤ dR α R hα hR

end

end RobinCaps.Transverse
