import Mathlib
import RobinCaps.Cap.Basic
import RobinCaps.Cap.Regular
import RobinCaps.Cap.Concave
import RobinCaps.Cap.Sharp
import RobinCaps.Cap.Volume

/-!
# Extension invariance: appending a straight cylinder to an admissible end cap

The manuscript's consistency check `sec:checks`
(`reference/robin_endcaps_corrected_en.tex`) observes that extending an
admissible end cap `C` at its entrance `s = -K` by a straight unit cylinder of
length `δ > 0` produces an admissible end cap whose functional
`𝓕 = |Γ| - m|C|` is unchanged: both the exposed area and `m` times the volume
grow by exactly `m ω_m δ`.

`RobinCaps/Cap/Sharp.lean` already contains this at the level of *raw profiles*
(`Cap.revF_append`).  This file upgrades it to the `Cap` structure:

* `Cap.appendθ C = fun s => if s ≤ -C.K then 1 else C.θ s` is the glued profile;
* `Cap.append C δ hδ : Cap m` is the extended cap (axial length `C.K + δ`);
* `Cap.append_lateralArea` / `Cap.append_revolutionArea`: the exposed area grows by
  `m ω_m δ`; `Cap.append_revolutionVolume`: the volume grows by `ω_m δ` (so
  `m Δ|C| = m ω_m δ`), which is the manuscript's bookkeeping;
* `Cap.append_revolutionF`, `Cap.append_F`, `Cap.append_beta`: the functional and
  hence `β` are unchanged.

## The junction

The only delicate admissibility field is concavity at the junction `s = -K`.
Note that the recorded value `C.θ (-C.K)` of an arbitrary `Cap` is *unconstrained*
(only the limit `θ(-K⁺) = 1` is recorded, via `Cap.θ_tendsto`), and concavity of
the glued profile genuinely forces the junction value to be `1`.  We therefore
glue with `≤` rather than `<`, i.e. we use the value `1` *at* `-C.K`:
`appendθ C = appendProfile C.K δ (appendθ C)` (`Cap.appendProfile_appendθ`), so
the raw-profile theorem `Cap.revF_append` applies verbatim.

Concavity across the junction is `Cap.appendθ_junction`: for `-K < p ≤ y < 0`
and `p = μ(-K) + (1-μ)y` one has `μ·1 + (1-μ)θ(y) ≤ θ(p)`.  This is obtained
from concavity of `θ` on `(-K,0)` at the pair `(z, y)` with `z ↘ -K`, together
with `θ(-K⁺) = 1`.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace RobinCaps
namespace Cap

noncomputable section

variable {m : ℕ}

/-! ### The glued profile -/

/-- The profile of the cap `C` extended at its entrance by a straight unit
cylinder: the constant `1` on `(-∞, -K]` and `C.θ` on `(-K, ∞)`. -/
def appendθ (C : Cap m) : ℝ → ℝ := fun s => if s ≤ -C.K then 1 else C.θ s

theorem appendθ_of_le (C : Cap m) {s : ℝ} (hs : s ≤ -C.K) : appendθ C s = 1 := if_pos hs

theorem appendθ_of_lt (C : Cap m) {s : ℝ} (hs : -C.K < s) : appendθ C s = C.θ s :=
  if_neg (not_le.2 hs)

/-- The glued profile is a fixed point of `appendProfile`: gluing the constant `1`
to the left of `-K` changes nothing, because `appendθ C` is already `1` there. -/
theorem appendProfile_appendθ (C : Cap m) (δ : ℝ) :
    appendProfile C.K δ (appendθ C) = appendθ C := by
  funext s
  rcases lt_or_ge s (-C.K) with h | h
  · rw [appendProfile_cyl _ _ _ h, appendθ_of_le C h.le]
  · rw [appendProfile, if_neg (not_lt.2 h)]

/-- Under the normalisation `C.θ (-C.K) = 1` — which is necessary for the glued
profile to be concave, and which holds for every `ProfileAC` cap
(`ProfileAC.entrance`) — the glued profile is *literally* the raw-profile gluing
`Cap.appendProfile` of `RobinCaps/Cap/Sharp.lean`. -/
theorem appendθ_eq_appendProfile (C : Cap m) (δ : ℝ) (hent : C.θ (-C.K) = 1) :
    appendθ C = appendProfile C.K δ C.θ := by
  funext s
  rcases lt_or_ge s (-C.K) with h | h
  · rw [appendθ_of_le C h.le, appendProfile_cyl _ _ _ h]
  · rw [appendProfile, if_neg (not_lt.2 h)]
    rcases eq_or_lt_of_le h with h' | h'
    · rw [← h', appendθ_of_le C le_rfl, hent]
    · rw [appendθ_of_lt C h']

/-- On the cap part the glued profile has the same derivative as `C.θ`. -/
theorem deriv_appendθ (C : Cap m) {s : ℝ} (hs : -C.K < s) :
    deriv (appendθ C) s = deriv C.θ s := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [isOpen_Ioi.mem_nhds hs] with t ht
  exact appendθ_of_lt C ht

/-! ### Concavity across the junction -/

/-- **Junction inequality.**  If `-K < p ≤ y < 0` and `p = μ·(-K) + (1-μ)·y`
(so automatically `μ ∈ [0,1)`), then `μ·1 + (1-μ)·θ(y) ≤ θ(p)`.

This is the chord inequality for the *closed* interval `[-K, y]`, where the
profile is given the value `1` at the left endpoint; it follows from concavity
on `(-K,0)` by letting the left endpoint `z` decrease to `-K`, using
`θ(-K⁺) = 1`. -/
theorem appendθ_junction (C : Cap m) {p y μ : ℝ} (hp : -C.K < p) (hpy : p ≤ y) (hy : y < 0)
    (hcomb : μ * (-C.K) + (1 - μ) * y = p) :
    μ + (1 - μ) * C.θ y ≤ C.θ p := by
  have hyI : y ∈ Ioo (-C.K) 0 := ⟨lt_of_lt_of_le hp hpy, hy⟩
  have hyK : 0 < y + C.K := by have := hyI.1; linarith
  -- the chord inequality with left endpoint `z ∈ (-K, p)`
  have key : ∀ z ∈ Ioo (-C.K) p,
      (y - p) / (y - z) * C.θ z + (1 - (y - p) / (y - z)) * C.θ y ≤ C.θ p := by
    intro z hz
    have hzp : z < p := hz.2
    have hzy : z < y := lt_of_lt_of_le hzp hpy
    have hyz : 0 < y - z := by linarith
    have hν0 : 0 ≤ (y - p) / (y - z) := div_nonneg (by linarith) hyz.le
    have hν1 : (y - p) / (y - z) ≤ 1 := by rw [div_le_one hyz]; linarith
    have hzI : z ∈ Ioo (-C.K) 0 := ⟨hz.1, by linarith⟩
    have hyzne : y - z ≠ 0 := hyz.ne'
    have hνmul : (y - p) / (y - z) * (y - z) = y - p := by field_simp
    have hcomb2 : (y - p) / (y - z) * z + (1 - (y - p) / (y - z)) * y = p := by
      linear_combination -hνmul
    have hν0' : (0 : ℝ) ≤ 1 - (y - p) / (y - z) := by linarith
    have hνsum : (y - p) / (y - z) + (1 - (y - p) / (y - z)) = 1 := by ring
    have hconc := C.θ_concave.2 hzI hyI hν0 hν0' hνsum
    simp only [smul_eq_mul] at hconc
    rwa [hcomb2] at hconc
  -- identify `μ`
  have hμeq : μ = (y - p) / (y + C.K) := by
    rw [eq_div_iff hyK.ne']
    linear_combination -hcomb
  -- pass to the limit `z ↘ -K`
  have hcont : ContinuousAt (fun z : ℝ => (y - p) / (y - z)) (-C.K) := by
    refine ContinuousAt.div continuousAt_const (by fun_prop) ?_
    rw [sub_neg_eq_add]
    exact hyK.ne'
  have h1 : Tendsto (fun z : ℝ => (y - p) / (y - z)) (𝓝[>] (-C.K)) (𝓝 ((y - p) / (y + C.K))) := by
    have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (-C.K)))
    rwa [sub_neg_eq_add] at this
  have hlim : Tendsto (fun z : ℝ => (y - p) / (y - z) * C.θ z + (1 - (y - p) / (y - z)) * C.θ y)
      (𝓝[>] (-C.K))
      (𝓝 ((y - p) / (y + C.K) * 1 + (1 - (y - p) / (y + C.K)) * C.θ y)) :=
    (h1.mul C.θ_tendsto).add ((tendsto_const_nhds.sub h1).mul tendsto_const_nhds)
  have hfinal : (y - p) / (y + C.K) * 1 + (1 - (y - p) / (y + C.K)) * C.θ y ≤ C.θ p := by
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT hp] with z hz
    exact key z hz
  rw [hμeq]
  linarith [hfinal]

/-- **Concavity of the glued profile** on the extended axial interval. -/
theorem appendθ_concaveOn (C : Cap m) (δ : ℝ) :
    ConcaveOn ℝ (Ioo (-(C.K + δ)) 0) (appendθ C) := by
  have hmain : ∀ x ∈ Ioo (-(C.K + δ)) 0, ∀ y ∈ Ioo (-(C.K + δ)) 0, x ≤ y →
      ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      a * appendθ C x + b * appendθ C y ≤ appendθ C (a * x + b * y) := by
    intro x hx y hy hxy a b ha hb hab
    have hb' : b = 1 - a := by linarith
    have hdx : a * x + b * y - x = b * (y - x) := by rw [hb']; ring
    have hdy : y - (a * x + b * y) = a * (y - x) := by rw [hb']; ring
    have hpx : x ≤ a * x + b * y := by
      have := mul_nonneg hb (sub_nonneg.2 hxy); linarith
    have hpy : a * x + b * y ≤ y := by
      have := mul_nonneg ha (sub_nonneg.2 hxy); linarith
    set p : ℝ := a * x + b * y with hpdef
    rcases le_or_gt y (-C.K) with hyK | hyK
    · rw [appendθ_of_le C (hxy.trans hyK), appendθ_of_le C hyK, appendθ_of_le C (hpy.trans hyK)]
      linarith
    rcases lt_or_ge (-C.K) x with hxK | hxK
    · -- entirely inside the original cap
      have hxI : x ∈ Ioo (-C.K) 0 := ⟨hxK, hx.2⟩
      have hyI : y ∈ Ioo (-C.K) 0 := ⟨hyK, hy.2⟩
      have hpI : -C.K < p := lt_of_lt_of_le hxK hpx
      rw [appendθ_of_lt C hxK, appendθ_of_lt C hyK, appendθ_of_lt C hpI]
      have hconc := C.θ_concave.2 hxI hyI ha hb hab
      simpa only [smul_eq_mul] using hconc
    · -- the chord crosses the junction: `x ≤ -K < y`
      have hyI : y ∈ Ioo (-C.K) 0 := ⟨hyK, hy.2⟩
      have hθy := C.θ_le_one y hyI
      rw [appendθ_of_le C hxK, appendθ_of_lt C hyK]
      rcases le_or_gt p (-C.K) with hpK | hpK
      · rw [appendθ_of_le C hpK]
        nlinarith
      · rw [appendθ_of_lt C hpK]
        have hyK' : 0 < y + C.K := by linarith
        have hyKne : y + C.K ≠ 0 := hyK'.ne'
        have hcomb : (y - p) / (y + C.K) * (-C.K) + (1 - (y - p) / (y + C.K)) * y = p := by
          field_simp
          ring
        have hj := appendθ_junction C hpK hpy hy.2 hcomb
        -- the chord from `(x, 1)` lies below the chord from `(-K, 1)`
        have hyp : y - p = a * (y - x) := by rw [hpdef, hb']; ring
        have hle : a ≤ (y - p) / (y + C.K) := by
          rw [le_div_iff₀ hyK']
          nlinarith
        nlinarith [mul_nonneg (sub_nonneg.2 hle) (sub_nonneg.2 hθy)]
  refine ⟨convex_Ioo _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  rcases le_total x y with h | h
  · exact hmain x hx y hy h a b ha hb hab
  · have hswap := hmain y hy x hx h b a hb ha (by linarith)
    rw [show a * x + b * y = b * y + a * x from by ring]
    linarith [hswap]

/-! ### The appended cap -/

/-- The profile of an appended cap tends to `1` at the new entrance: it is
*constant* equal to `1` there. -/
theorem appendθ_tendsto (C : Cap m) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (appendθ C) (𝓝[>] (-(C.K + δ))) (𝓝 1) := by
  refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (1 : ℝ)))
  have hmem : Iio (-C.K) ∈ 𝓝[>] (-(C.K + δ)) :=
    mem_nhdsWithin_of_mem_nhds (isOpen_Iio.mem_nhds (by simp only [mem_Iio]; linarith))
  filter_upwards [hmem] with z hz
  exact (appendθ_of_le C (le_of_lt hz)).symm

/-- **The appended cap.**  `C.append δ hδ` is the admissible end cap obtained from
`C` by prepending a straight unit cylinder of length `δ` at the entrance:
axial length `C.K + δ`, profile `appendθ C`. -/
def append (C : Cap m) (δ : ℝ) (hδ : 0 < δ) : Cap m where
  K := C.K + δ
  hK := by linarith [C.hK]
  θ := appendθ C
  θ_pos := by
    intro s hs
    rcases le_or_gt s (-C.K) with h | h
    · rw [appendθ_of_le C h]; norm_num
    · rw [appendθ_of_lt C h]; exact C.θ_pos s ⟨h, hs.2⟩
  θ_le_one := by
    intro s hs
    rcases le_or_gt s (-C.K) with h | h
    · rw [appendθ_of_le C h]
    · rw [appendθ_of_lt C h]; exact C.θ_le_one s ⟨h, hs.2⟩
  θ_concave := appendθ_concaveOn C δ
  θ_antitone := by
    intro x hx y hy hxy
    rcases le_or_gt y (-C.K) with h | h
    · rw [appendθ_of_le C h, appendθ_of_le C (hxy.trans h)]
    · rw [appendθ_of_lt C h]
      rcases le_or_gt x (-C.K) with h' | h'
      · rw [appendθ_of_le C h']; exact C.θ_le_one y ⟨h, hy.2⟩
      · rw [appendθ_of_lt C h']; exact C.θ_antitone ⟨h', hx.2⟩ ⟨h, hy.2⟩ hxy
  θ_tendsto := appendθ_tendsto C hδ
  θ_entrance := appendθ_of_le C (by linarith [C.hK])
  θ_terminal := by
    have hval : appendθ C 0 = C.θ 0 := appendθ_of_lt C (by linarith [C.hK])
    rw [hval]
    refine Tendsto.congr' ?_ C.θ_terminal
    have hmem : Ioi (-C.K) ∈ 𝓝[<] (0 : ℝ) :=
      mem_nhdsWithin_of_mem_nhds
        (isOpen_Ioi.mem_nhds (by simp only [mem_Ioi]; linarith [C.hK]))
    filter_upwards [hmem] with z hz
    exact (appendθ_of_lt C hz).symm

@[simp] theorem append_K (C : Cap m) (δ : ℝ) (hδ : 0 < δ) : (C.append δ hδ).K = C.K + δ := rfl

@[simp] theorem append_θ (C : Cap m) (δ : ℝ) (hδ : 0 < δ) : (C.append δ hδ).θ = appendθ C := rfl

/-- The appended cap has entrance value exactly `1` (the new entrance sits on the
straight cylinder). -/
theorem append_theta_entrance (C : Cap m) (δ : ℝ) (hδ : 0 < δ) :
    (C.append δ hδ).θ (-(C.K + δ)) = 1 :=
  appendθ_of_le C (by linarith)

/-- The appended cap has the same terminal radius. -/
theorem append_theta_terminal (C : Cap m) (δ : ℝ) (hδ : 0 < δ) :
    (C.append δ hδ).θ 0 = C.θ 0 :=
  appendθ_of_lt C (by linarith [C.hK])

/-! ### Invariance of the functional -/

section Invariance

variable (C : Cap m) (δ : ℝ) (hδ : 0 < δ)

private theorem ae_cap_part :
    ∀ᵐ z ∂(volume.restrict (uIoc (-C.K) (0 : ℝ))), -C.K < z := by
  rw [uIoc_of_le (by linarith [C.hK] : (-C.K : ℝ) ≤ 0)]
  exact ae_gt_of_ae_restrict_Ioc

private theorem lateral_ae :
    (fun s => (appendθ C s) ^ (m - 1) * Real.sqrt (1 + (deriv (appendθ C) s) ^ 2))
      =ᵐ[volume.restrict (uIoc (-C.K) (0 : ℝ))]
      (fun s => (C.θ s) ^ (m - 1) * Real.sqrt (1 + (deriv C.θ s) ^ 2)) := by
  filter_upwards [ae_cap_part C] with z hz
  rw [appendθ_of_lt C hz, deriv_appendθ C hz]

private theorem volume_ae :
    (fun s => (appendθ C s) ^ m)
      =ᵐ[volume.restrict (uIoc (-C.K) (0 : ℝ))] (fun s => (C.θ s) ^ m) := by
  filter_upwards [ae_cap_part C] with z hz
  rw [appendθ_of_lt C hz]

/-- The volume integrand of a cap profile is interval integrable. -/
theorem volume_intervalIntegrable :
    IntervalIntegrable (fun s => (C.θ s) ^ m) volume (-C.K) 0 := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith [C.hK])]
  exact C.integrableOn_pow (Concave.continuousOn_Ioo C)

/-- The area element of the glued profile is interval integrable on the cap part. -/
private theorem lateral_intervalIntegrable_appendθ :
    IntervalIntegrable
      (fun s => (appendθ C s) ^ (m - 1) * Real.sqrt (1 + (deriv (appendθ C) s) ^ 2))
      volume (-C.K) 0 :=
  (Concave.areaElement_intervalIntegrable C).congr_ae (lateral_ae C).symm

private theorem volume_intervalIntegrable_appendθ :
    IntervalIntegrable (fun s => (appendθ C s) ^ m) volume (-C.K) 0 :=
  (volume_intervalIntegrable C).congr_ae (volume_ae C).symm

/-- **The lateral area grows by `m ω_m δ`** (manuscript `sec:checks`: `ΔH = m ω_m δ`). -/
theorem append_lateralArea :
    (C.append δ hδ).lateralArea = C.lateralArea + (m : ℝ) * omega m * δ := by
  have h := lateral_integral_append m C.K δ hδ C.hK (appendθ C)
    (lateral_intervalIntegrable_appendθ C)
  rw [appendProfile_appendθ] at h
  have h2 : (∫ s in (-C.K)..0, (appendθ C s) ^ (m - 1) *
        Real.sqrt (1 + (deriv (appendθ C) s) ^ 2))
      = ∫ s in (-C.K)..0, (C.θ s) ^ (m - 1) * Real.sqrt (1 + (deriv C.θ s) ^ 2) :=
    intervalIntegral.integral_congr_ae ((ae_restrict_iff' measurableSet_uIoc).mp (lateral_ae C))
  simp only [lateralArea, append_K, append_θ]
  rw [h, h2]
  ring

/-- The terminal disk is unchanged by the extension. -/
theorem append_terminalArea : (C.append δ hδ).terminalArea = C.terminalArea := by
  simp only [terminalArea, append_θ, appendθ_of_lt C (by linarith [C.hK] : (-C.K : ℝ) < 0)]

/-- **The exposed area grows by `m ω_m δ`.** -/
theorem append_revolutionArea :
    (C.append δ hδ).revolutionArea = C.revolutionArea + (m : ℝ) * omega m * δ := by
  simp only [revolutionArea, append_lateralArea C δ hδ, append_terminalArea C δ hδ]
  ring

/-- **The volume grows by `ω_m δ`** (manuscript `sec:checks`: `m Δ|C| = m ω_m δ`). -/
theorem append_revolutionVolume :
    (C.append δ hδ).revolutionVolume = C.revolutionVolume + omega m * δ := by
  have h := volume_integral_append m C.K δ hδ C.hK (appendθ C)
    (volume_intervalIntegrable_appendθ C)
  rw [appendProfile_appendθ] at h
  have h2 : (∫ s in (-C.K)..0, (appendθ C s) ^ m) = ∫ s in (-C.K)..0, (C.θ s) ^ m :=
    intervalIntegral.integral_congr_ae ((ae_restrict_iff' measurableSet_uIoc).mp (volume_ae C))
  simp only [revolutionVolume, append_K, append_θ]
  rw [h, h2]
  ring

/-- **Extension invariance of the functional.**  Appending a straight unit
cylinder of length `δ` at the entrance does not change `𝓕`: the exposed area and
`m` times the volume both increase by `m ω_m δ` (manuscript `sec:checks`). -/
theorem append_revolutionF : (C.append δ hδ).revolutionF = C.revolutionF := by
  have hAL : IntervalIntegrable
      (fun s => (appendθ C s) ^ (m - 1) * Real.sqrt (1 + (deriv (appendθ C) s) ^ 2))
      volume (-C.K) 0 :=
    (Concave.areaElement_intervalIntegrable C).congr_ae (lateral_ae C).symm
  have hAV : IntervalIntegrable (fun s => (appendθ C s) ^ m) volume (-C.K) 0 :=
    (volume_intervalIntegrable C).congr_ae (volume_ae C).symm
  have h1 : revF m (C.K + δ) (appendθ C) = revF m C.K (appendθ C) := by
    have := revF_append m C.K δ hδ C.hK (appendθ C) hAL hAV
    rwa [appendProfile_appendθ] at this
  have h2 : revF m C.K (appendθ C) = revF m C.K C.θ := by
    simp only [revF, revLateral, revVolume, revTerminal]
    rw [intervalIntegral.integral_congr_ae
        ((ae_restrict_iff' measurableSet_uIoc).mp (lateral_ae C)),
      intervalIntegral.integral_congr_ae
        ((ae_restrict_iff' measurableSet_uIoc).mp (volume_ae C)),
      appendθ_of_lt C (by linarith [C.hK] : (-C.K : ℝ) < 0)]
  rw [revF_eq m (C.append δ hδ), revF_eq m C]
  exact h1.trans h2

/-- The paper's functional `𝓕` is unchanged by the extension. -/
theorem append_F : (C.append δ hδ).F = C.F := append_revolutionF C δ hδ

/-- The effective end coefficient `β` is unchanged by the extension. -/
theorem append_beta (α : ℝ) : (C.append δ hδ).beta α = C.beta α := by
  simp only [beta, append_F C δ hδ]

end Invariance

/-! ### Regularity of the appended cap -/

/-- Left-continuity at the terminal point is inherited by the appended cap. -/
theorem append_terminalContinuous (C : Cap m) (δ : ℝ) (hδ : 0 < δ)
    (h : TerminalContinuous C) : TerminalContinuous (C.append δ hδ) := by
  have hval : appendθ C 0 = C.θ 0 := appendθ_of_lt C (by linarith [C.hK])
  show Tendsto (appendθ C) (𝓝[<] (0 : ℝ)) (𝓝 (appendθ C 0))
  rw [hval]
  refine Tendsto.congr' ?_ h
  have hmem : Ioi (-C.K) ∈ 𝓝[<] (0 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds
      (isOpen_Ioi.mem_nhds (by simp only [mem_Ioi]; linarith [C.hK]))
  filter_upwards [hmem] with z hz
  exact (appendθ_of_lt C hz).symm

/-- `ProfileAC` for the appended cap: it needs only left-continuity of `C.θ` at the
terminal point (the entrance value is automatically `1`). -/
theorem append_profileAC (C : Cap m) (δ : ℝ) (hδ : 0 < δ)
    (h : TerminalContinuous C) : ProfileAC (C.append δ hδ) :=
  Concave.profileAC_of_cap (C.append δ hδ) (append_theta_entrance C δ hδ)
    (append_terminalContinuous C δ hδ h)

/-- A `ProfileAC` cap is in particular left-continuous at the terminal point. -/
theorem TerminalContinuous.of_profileAC {C : Cap m} (h : ProfileAC C) :
    TerminalContinuous C := by
  have hK0 : (-C.K : ℝ) ≤ 0 := by linarith [C.hK]
  have hmem : Icc (-C.K) (0 : ℝ) ∈ 𝓝[<] (0 : ℝ) := by
    have hI : Ioi (-C.K) ∈ 𝓝[<] (0 : ℝ) :=
      mem_nhdsWithin_of_mem_nhds
        (isOpen_Ioi.mem_nhds (by simp only [mem_Ioi]; linarith [C.hK]))
    filter_upwards [self_mem_nhdsWithin, hI] with z hz1 hz2
    exact ⟨le_of_lt hz2, le_of_lt hz1⟩
  exact (h.continuousOn 0 (right_mem_Icc.2 hK0)).mono_left (nhdsWithin_le_iff.2 hmem)

/-- `ProfileAC` is inherited by the appended cap. -/
theorem append_profileAC_of_profileAC (C : Cap m) (δ : ℝ) (hδ : 0 < δ)
    (h : ProfileAC C) : ProfileAC (C.append δ hδ) :=
  append_profileAC C δ hδ (TerminalContinuous.of_profileAC h)

/-- Appending twice is appending once, with the lengths added. -/
theorem append_append (C : Cap m) (δ₁ δ₂ : ℝ) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) :
    ((C.append δ₁ hδ₁).append δ₂ (by linarith)).θ = (C.append (δ₁ + δ₂) (by linarith)).θ := by
  funext s
  show appendθ (C.append δ₁ hδ₁) s = appendθ C s
  rcases le_or_gt s (-(C.K + δ₁)) with h | h
  · rw [appendθ_of_le (C.append δ₁ hδ₁) (by simpa only [append_K] using h),
      appendθ_of_le C (by linarith)]
  · rw [appendθ_of_lt (C.append δ₁ hδ₁) (by simpa only [append_K] using h), append_θ]

end

end Cap
end RobinCaps


