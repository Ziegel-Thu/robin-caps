import RobinCaps.Hausdorff.IsodiamIface
import RobinCaps.Hausdorff.LinearImage

/-!
# The value of the Hausdorff normalising constant (wave 13)

This file proves `HConstValueProp m` (declared in `RobinCaps.Hausdorff.IsodiamIface`): the
normalising constant `hConst m` from `RobinCaps.Hausdorff.AreaIface` equals `2^m / ω_m`, where
`ω_m := volume (ball 0 1)` in `E := EuclideanSpace ℝ (Fin m)`. Equivalently, since
`μH[m] = hConst m • volume` (`hausdorffVolume_hlin`), this says
`μH[m] (ball 0 1) = 2^m` (the two statements are the same after multiplying by
`ω_m = volume (ball 0 1)`, which is finite and positive, so it cancels).

The isodiametric inequality (`IsodiametricProp`, proved elsewhere by Steiner symmetrisation) is
taken as a hypothesis `hI`.

* `m = 0`: `E` is a single point, `ball 0 1 = closedBall 0 1 = univ`, `μH[0] univ = 1`
  (`hausdorffMeasure_zero_singleton`), and both sides of `HConstValueProp 0` reduce to
  `1 / volume univ`.

* `m ≥ 1`:
  - **Lower bound** `2^m/ω ≤ hConst m`. We show the *global* measure inequality
    `(2^m/ω) • volume ≤ μH[m]` via `Measure.le_hausdorffMeasure`, which reduces to: for every
    set `s`, `(2^m/ω) * volume s ≤ (diam s)^m` (`hKey`). If `diam s = ∞` this is trivial; if
    `diam s < ∞`, `closure s` is compact (bounded + closed in a finite-dimensional space) and the
    isodiametric inequality bounds `volume (closure s) ≤ volume (closedBall 0 (diam s / 2))
    = ω (diam s / 2)^m`, which rearranges (using `2^m/ω * ω = 2^m`) to the claim.  Evaluating the
    global inequality at `U := ball 0 1` and using `volume U = ω` gives `2^m ≤ μH[m] U`.

  - **Upper bound** `μH[m] U ≤ 2^m`. For every `n`, Besicovitch's covering theorem
    (`Besicovitch.exists_disjoint_closedBall_covering_ae`) gives countably many pairwise disjoint
    closed balls `closedBall x (r x) ⊆ U` with `x` ranging over a countable `t n ⊆ U` and radii
    `< 1/(n+1)`, covering `U` up to a `volume`-null set `N n`. Since `μH[m] = hConst m • volume`,
    each `N n` is also `μH[m]`-null, hence so is `⋃ n, N n`; set `s := U \ ⋃ n, N n`. At each stage
    `n`, `s` is covered by the balls of stage `n` (diameter `< 2/(n+1) → 0`), so
    `Measure.hausdorffMeasure_le_liminf_tsum` bounds `μH[m] s` by the `liminf` over `n` of
    `∑' i, diam (ball i)^m`; using disjointness (`measure_iUnion`), each such sum is
    `≤ (2^m/ω) * volume U = 2^m` (again via `2^m/ω * ω = 2^m`), a bound independent of `n`, so the
    `liminf` is `≤ 2^m`. Hence `μH[m] U ≤ μH[m] s + μH[m] (⋃ n, N n) = μH[m] s ≤ 2^m`.

  Combining both bounds with `hConst m * ω = μH[m] U` (from `hausdorffVolume_hlin`) and
  `0 < ω < ∞` gives `hConst m = 2^m/ω`.

No `sorry`/hypothesis besides the isodiametric inequality `hI`, which is proved by a parallel
worker in `RobinCaps.Hausdorff.IsodiamIface`'s companion files.
-/

noncomputable section

open MeasureTheory Set Metric Filter Function
open scoped ENNReal Topology

namespace RobinCaps.Hausdorff

/-- **The value of the Hausdorff normalising constant**: `hConst m = 2^m / ω_m`, where
`ω_m = volume (ball 0 1)` in `EuclideanSpace ℝ (Fin m)`, assuming the isodiametric inequality. -/
theorem hConstValue_hcv (m : ℕ) (hI : IsodiametricProp m) : HConstValueProp m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- `m = 0`: `E` is a single point.
    haveI hsub : Subsingleton (EuclideanSpace ℝ (Fin 0)) :=
      Module.finrank_zero_iff.mp finrank_euclideanSpace_fin
    haveI hu : Unique (EuclideanSpace ℝ (Fin 0)) := uniqueOfSubsingleton 0
    have hball : ball (0 : EuclideanSpace ℝ (Fin 0)) 1 = (univ : Set (EuclideanSpace ℝ (Fin 0))) :=
      eq_univ_of_forall fun x => by
        have hx0 : x = (0 : EuclideanSpace ℝ (Fin 0)) := Subsingleton.elim _ _
        simp [Metric.mem_ball, hx0]
    have hcball :
        closedBall (0 : EuclideanSpace ℝ (Fin 0)) 1 = (univ : Set (EuclideanSpace ℝ (Fin 0))) :=
      eq_univ_of_forall fun x => by
        have hx0 : x = (0 : EuclideanSpace ℝ (Fin 0)) := Subsingleton.elim _ _
        simp [Metric.mem_closedBall, hx0]
    have hHM :
        (Measure.hausdorffMeasure ((0 : ℕ) : ℝ) : Measure (EuclideanSpace ℝ (Fin 0)))
            (univ : Set (EuclideanSpace ℝ (Fin 0))) = 1 := by
      rw [Set.univ_unique]
      simp
    unfold HConstValueProp
    unfold hConst
    rw [hcball, hball, hHM]
    norm_num
  · -- `m ≥ 1`.
    set E := EuclideanSpace ℝ (Fin m) with hE_def
    set ω : ℝ≥0∞ := volume (ball (0 : E) 1) with hω_def
    have hfr : Module.finrank ℝ E = m := finrank_euclideanSpace_fin
    haveI hNT : Nontrivial E :=
      Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hfr]; exact hm)
    have hω_pos : 0 < ω := Metric.measure_ball_pos volume (0 : E) one_pos
    have hω_fin : ω < ∞ :=
      lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall)
        (isCompact_closedBall (0 : E) 1).measure_lt_top
    have hω_ne0 : ω ≠ 0 := hω_pos.ne'
    have hω_net : ω ≠ ∞ := hω_fin.ne
    have h2 : (2 : ℝ≥0∞) ^ m = ENNReal.ofReal ((2 : ℝ) ^ m) := by
      rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2) m]
      norm_num
    have hvol_closedBall : ∀ (x : E) {r : ℝ}, 0 ≤ r →
        volume (closedBall x r) = ENNReal.ofReal (r ^ m) * ω := by
      intro x r hr
      rw [Measure.addHaar_closedBall volume x hr, hfr]
    -- `(2^m/ω) * volume (closedBall x ρ) = ofReal ((2ρ)^m)` for `ρ ≥ 0`.
    have heq_ball : ∀ (x : E) {ρ : ℝ}, 0 ≤ ρ →
        (2 : ℝ≥0∞) ^ m / ω * volume (closedBall x ρ) = ENNReal.ofReal ((2 * ρ) ^ m) := by
      intro x ρ hρ
      rw [hvol_closedBall x hρ, mul_left_comm, ENNReal.div_mul_cancel hω_ne0 hω_net, h2,
        ← ENNReal.ofReal_mul (by positivity), mul_pow, mul_comm]
    -- **Key inequality**: the isodiametric bound, for every set, in `EMetric`/`rpow` form.
    have hKey : ∀ s : Set E,
        (2 : ℝ≥0∞) ^ m / ω * volume s ≤ EMetric.diam s ^ (m : ℝ) := by
      intro s
      rcases s.eq_empty_or_nonempty with rfl | hne
      · simp
      by_cases hfin : EMetric.diam s = ⊤
      · rw [hfin, ENNReal.top_rpow_of_pos (by exact_mod_cast hm)]
        exact le_top
      · have hb : Bornology.IsBounded s := Metric.isBounded_iff_ediam_ne_top.2 hfin
        have hK : IsCompact (closure s) := hb.isCompact_closure
        have hiso := hI (closure s) hK
        rw [Metric.diam_closure] at hiso
        have hvol_le : volume s ≤ volume (closedBall (0 : E) (Metric.diam s / 2)) :=
          le_trans (measure_mono subset_closure) hiso
        have hed : ENNReal.ofReal (Metric.diam s) = EMetric.diam s := ENNReal.ofReal_toReal hfin
        calc (2 : ℝ≥0∞) ^ m / ω * volume s
            ≤ (2 : ℝ≥0∞) ^ m / ω * volume (closedBall (0 : E) (Metric.diam s / 2)) :=
              mul_le_mul_left' hvol_le _
          _ = ENNReal.ofReal ((2 * (Metric.diam s / 2)) ^ m) :=
              heq_ball (0 : E) (by positivity)
          _ = ENNReal.ofReal (Metric.diam s ^ m) := by
              congr 2
              ring
          _ = (ENNReal.ofReal (Metric.diam s)) ^ m := ENNReal.ofReal_pow Metric.diam_nonneg m
          _ = EMetric.diam s ^ m := by rw [hed]
          _ = EMetric.diam s ^ (m : ℝ) := (ENNReal.rpow_natCast _ m).symm
    -- **Lower bound**: `2^m/ω ≤ hConst m`.
    have hLower : (2 : ℝ≥0∞) ^ m / ω * ω
        ≤ (Measure.hausdorffMeasure (m : ℝ) : Measure E) (ball (0 : E) 1) := by
      have hle : ((2 : ℝ≥0∞) ^ m / ω) • (volume : Measure E)
          ≤ (Measure.hausdorffMeasure (m : ℝ) : Measure E) :=
        Measure.le_hausdorffMeasure (m : ℝ) _ ⊤ ENNReal.zero_lt_top
          (fun s _ => by
            have h := hKey s
            simpa using h)
      have := Measure.le_iff'.mp hle (ball (0 : E) 1)
      simpa using this
    rw [ENNReal.div_mul_cancel hω_ne0 hω_net] at hLower
    -- `hLower : 2 ^ m ≤ μH[m] (ball 0 1)`
    -- **Upper bound**: `μH[m] (ball 0 1) ≤ 2^m`, via a Besicovitch covering.
    set U : Set E := ball (0 : E) 1 with hU_def
    have hUopen : IsOpen U := Metric.isOpen_ball
    have hadmissible : ∀ n : ℕ, ∀ x ∈ U, ∀ ε : ℝ, 0 < ε →
        (({ρ : ℝ | closedBall x ρ ⊆ U} ∩ Set.Ioo (0 : ℝ) (1 / (n + 1))) ∩
            Set.Ioo (0 : ℝ) ε).Nonempty := by
      intro n x hx ε hε
      have hxU : dist x (0 : E) < 1 := by simpa [U, Metric.mem_ball] using hx
      set ε₀ : ℝ := (1 - dist x (0 : E)) / 2 with hε₀_def
      have hε₀pos : 0 < ε₀ := by rw [hε₀_def]; linarith
      have hballsub : closedBall x ε₀ ⊆ U := by
        intro y hy
        have hyx : dist y x ≤ ε₀ := hy
        have hy0 : dist y (0 : E) < 1 := by
          calc dist y (0 : E) ≤ dist y x + dist x 0 := dist_triangle _ _ _
            _ ≤ ε₀ + dist x 0 := by linarith
            _ < 1 := by rw [hε₀_def]; linarith
        simpa [U, Metric.mem_ball] using hy0
      refine ⟨min ε₀ (min (1 / ((n : ℝ) + 1)) ε) / 2, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
      · exact closedBall_subset_closedBall (by
          calc min ε₀ (min (1 / ((n:ℝ)+1)) ε) / 2 ≤ ε₀ / 2 := by gcongr; exact min_le_left _ _
            _ ≤ ε₀ := by linarith) |>.trans hballsub
      · positivity
      · have : min ε₀ (min (1 / ((n:ℝ)+1)) ε) / 2 ≤ (1 / ((n:ℝ)+1)) / 2 := by
          gcongr
          exact (min_le_right _ _).trans (min_le_left _ _)
        have hpos1 : (0:ℝ) < 1 / ((n:ℝ)+1) := by positivity
        linarith
      · positivity
      · have : min ε₀ (min (1 / ((n:ℝ)+1)) ε) / 2 ≤ ε / 2 := by
          gcongr
          exact (min_le_right _ _).trans (min_le_right _ _)
        linarith
    have hbesicovitch : ∀ n : ℕ, ∃ (t : Set E) (r : E → ℝ), t.Countable ∧ t ⊆ U ∧
        (∀ x ∈ t, r x ∈ ({ρ : ℝ | closedBall x ρ ⊆ U} ∩ Set.Ioo (0 : ℝ) (1 / (n + 1))) ∩
            Set.Ioo (0 : ℝ) (1 : ℝ)) ∧
        volume (U \ ⋃ x ∈ t, closedBall x (r x)) = 0 ∧
        t.PairwiseDisjoint (fun x => closedBall x (r x)) := by
      intro n
      exact Besicovitch.exists_disjoint_closedBall_covering_ae volume
        (fun x => {ρ : ℝ | closedBall x ρ ⊆ U} ∩ Set.Ioo (0 : ℝ) (1 / (n + 1))) U
        (hadmissible n) (fun _ => (1 : ℝ)) (fun _ _ => one_pos)
    choose tf rf htc hts hb using hbesicovitch
    -- unpack `hb` into the four remaining pieces
    have htr : ∀ n : ℕ, ∀ x ∈ tf n,
        (closedBall x (rf n x) ⊆ U ∧ rf n x ∈ Set.Ioo (0 : ℝ) (1 / (n + 1))) ∧
          rf n x ∈ Set.Ioo (0 : ℝ) (1 : ℝ) := fun n x hx => (hb n).1 x hx
    have htmeas : ∀ n : ℕ, volume (U \ ⋃ x ∈ tf n, closedBall x (rf n x)) = 0 := fun n => (hb n).2.1
    have htdisj : ∀ n : ℕ, (tf n).PairwiseDisjoint (fun x => closedBall x (rf n x)) :=
      fun n => (hb n).2.2
    set Nn : ℕ → Set E := fun n => U \ ⋃ x ∈ tf n, closedBall x (rf n x) with hNn_def
    have hNnull : ∀ n, volume (Nn n) = 0 := htmeas
    have hProp1 := hausdorffVolume_hlin m
    have hHeq : (Measure.hausdorffMeasure (m : ℝ) : Measure E) = hConst m • volume := hProp1.1
    have hHnull : ∀ n, (Measure.hausdorffMeasure (m : ℝ) : Measure E) (Nn n) = 0 := by
      intro n
      rw [hHeq]
      show hConst m * volume (Nn n) = 0
      rw [hNnull n, mul_zero]
    have hHnull_union :
        (Measure.hausdorffMeasure (m : ℝ) : Measure E) (⋃ n, Nn n) = 0 := by
      apply le_antisymm _ (zero_le _)
      calc (Measure.hausdorffMeasure (m : ℝ) : Measure E) (⋃ n, Nn n)
          ≤ ∑' n, (Measure.hausdorffMeasure (m : ℝ) : Measure E) (Nn n) := measure_iUnion_le _
        _ = 0 := by simp [hHnull]
    set s : Set E := U \ ⋃ n, Nn n with hs_def
    have hUsub : U ⊆ s ∪ ⋃ n, Nn n := by
      intro x hx
      by_cases hxs : x ∈ ⋃ n, Nn n
      · exact Or.inr hxs
      · exact Or.inl ⟨hx, hxs⟩
    have hUle : (Measure.hausdorffMeasure (m : ℝ) : Measure E) U
        ≤ (Measure.hausdorffMeasure (m : ℝ) : Measure E) s
          + (Measure.hausdorffMeasure (m : ℝ) : Measure E) (⋃ n, Nn n) :=
      le_trans (measure_mono hUsub) (measure_union_le _ _)
    rw [hHnull_union, add_zero] at hUle
    -- Now bound `μH[m] s` via the covering at each stage `n`.
    have hballsubU : ∀ n : ℕ, ∀ x ∈ tf n, closedBall x (rf n x) ⊆ U := fun n x hx => (htr n x hx).1.1
    have hrpos : ∀ n : ℕ, ∀ x ∈ tf n, 0 < rf n x := fun n x hx => (htr n x hx).1.2.1
    have hrlt : ∀ n : ℕ, ∀ x ∈ tf n, rf n x < 1 / ((n : ℝ) + 1) :=
      fun n x hx => (htr n x hx).1.2.2
    haveI hCnt : ∀ n : ℕ, Countable (tf n) := fun n => (htc n).to_subtype
    have hCoverBound : ∀ n : ℕ,
        ∑' i : tf n, EMetric.diam (closedBall (i : E) (rf n i)) ^ (m : ℝ) ≤ (2 : ℝ≥0∞) ^ m := by
      intro n
      have hballbound : ∀ i : tf n,
          EMetric.diam (closedBall (i : E) (rf n i)) ^ (m : ℝ)
            ≤ (2 : ℝ≥0∞) ^ m / ω * volume (closedBall (i : E) (rf n i)) := by
        intro i
        have hρ0 : 0 ≤ rf n (i : E) := (hrpos n i i.2).le
        have hd1 : EMetric.diam (closedBall (i : E) (rf n i)) ≤ ENNReal.ofReal (2 * rf n i) := by
          have hne : EMetric.diam (closedBall (i : E) (rf n i)) ≠ ⊤ :=
            Metric.isBounded_closedBall.ediam_ne_top
          have hdle : Metric.diam (closedBall (i : E) (rf n i)) ≤ 2 * rf n i :=
            Metric.diam_closedBall hρ0
          calc EMetric.diam (closedBall (i : E) (rf n i))
              = ENNReal.ofReal (Metric.diam (closedBall (i : E) (rf n i))) :=
                (ENNReal.ofReal_toReal hne).symm
            _ ≤ ENNReal.ofReal (2 * rf n i) := ENNReal.ofReal_le_ofReal hdle
        calc EMetric.diam (closedBall (i : E) (rf n i)) ^ (m : ℝ)
            ≤ (ENNReal.ofReal (2 * rf n i)) ^ (m : ℝ) :=
              ENNReal.rpow_le_rpow hd1 (by positivity)
          _ = ENNReal.ofReal ((2 * rf n i) ^ m) := by
              rw [ENNReal.rpow_natCast, ENNReal.ofReal_pow (by positivity)]
          _ = (2 : ℝ≥0∞) ^ m / ω * volume (closedBall (i : E) (rf n i)) :=
              (heq_ball (i : E) hρ0).symm
      have hdisj' :
          Pairwise (Disjoint on fun i : tf n => closedBall (i : E) (rf n i)) := by
        intro i j hij
        exact htdisj n i.2 j.2 (fun h => hij (Subtype.ext h))
      calc ∑' i : tf n, EMetric.diam (closedBall (i : E) (rf n i)) ^ (m : ℝ)
          ≤ ∑' i : tf n, (2 : ℝ≥0∞) ^ m / ω * volume (closedBall (i : E) (rf n i)) :=
            ENNReal.tsum_le_tsum hballbound
        _ = (2 : ℝ≥0∞) ^ m / ω * ∑' i : tf n, volume (closedBall (i : E) (rf n i)) :=
            ENNReal.tsum_mul_left
        _ = (2 : ℝ≥0∞) ^ m / ω * volume (⋃ i : tf n, closedBall (i : E) (rf n i)) := by
            rw [measure_iUnion hdisj' (fun i => measurableSet_closedBall)]
        _ ≤ (2 : ℝ≥0∞) ^ m / ω * volume U := by
            gcongr
            rintro y hy
            simp only [Set.mem_iUnion] at hy
            obtain ⟨i, hy⟩ := hy
            exact hballsubU n (i : E) i.2 hy
        _ = (2 : ℝ≥0∞) ^ m := by
            rw [hU_def, ← hω_def, ENNReal.div_mul_cancel hω_ne0 hω_net]
    have hst : ∀ n : ℕ, s ⊆ ⋃ i : tf n, closedBall (i : E) (rf n i) := by
      intro n x hx
      have hxU : x ∈ U := hx.1
      have hxNn : x ∉ Nn n := fun h => hx.2 (Set.mem_iUnion.2 ⟨n, h⟩)
      rw [hNn_def] at hxNn
      simp only [Set.mem_diff, not_and, not_not] at hxNn
      have := hxNn hxU
      simp only [Set.mem_iUnion] at this ⊢
      obtain ⟨i, hiT, hi⟩ := this
      exact ⟨⟨i, hiT⟩, hi⟩
    have hr : Tendsto (fun n : ℕ => ENNReal.ofReal (2 * (1 / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2' : Tendsto (fun n : ℕ => (2 : ℝ) * (1 / (n + 1))) atTop (𝓝 (2 * 0)) :=
        h1.const_mul 2
      rw [mul_zero] at h2'
      have h3 := ENNReal.tendsto_ofReal h2'
      simpa using h3
    have htbound : ∀ᶠ n : ℕ in atTop, ∀ i : tf n,
        EMetric.diam (closedBall (i : E) (rf n i)) ≤ ENNReal.ofReal (2 * (1 / ((n : ℝ) + 1))) := by
      refine Filter.Eventually.of_forall (fun n i => ?_)
      have hρ0 : 0 ≤ rf n (i : E) := (hrpos n i i.2).le
      have hne : EMetric.diam (closedBall (i : E) (rf n i)) ≠ ⊤ :=
        Metric.isBounded_closedBall.ediam_ne_top
      have hdle : Metric.diam (closedBall (i : E) (rf n i)) ≤ 2 * rf n i :=
        Metric.diam_closedBall hρ0
      have hrlt' : rf n (i : E) ≤ 1 / ((n : ℝ) + 1) := (hrlt n i i.2).le
      calc EMetric.diam (closedBall (i : E) (rf n i))
          = ENNReal.ofReal (Metric.diam (closedBall (i : E) (rf n i))) :=
            (ENNReal.ofReal_toReal hne).symm
        _ ≤ ENNReal.ofReal (2 * (1 / ((n : ℝ) + 1))) :=
            ENNReal.ofReal_le_ofReal (by linarith)
    have hle_liminf :
        (Measure.hausdorffMeasure (m : ℝ) : Measure E) s
          ≤ liminf (fun n : ℕ => ∑' i : tf n, EMetric.diam (closedBall (i : E) (rf n i)) ^ (m : ℝ))
              atTop :=
      Measure.hausdorffMeasure_le_liminf_tsum (m : ℝ) s
        (fun n : ℕ => ENNReal.ofReal (2 * (1 / ((n : ℝ) + 1)))) hr
        (fun n (i : tf n) => closedBall (i : E) (rf n i)) htbound
        (Filter.Eventually.of_forall hst)
    have hUpper : (Measure.hausdorffMeasure (m : ℝ) : Measure E) U ≤ (2 : ℝ≥0∞) ^ m := by
      refine hUle.trans (hle_liminf.trans ?_)
      set g : ℕ → ℝ≥0∞ := fun n => ∑' i : tf n, EMetric.diam (closedBall (i : E) (rf n i)) ^ (m : ℝ)
      calc liminf g atTop
          ≤ liminf (fun _ : ℕ => (2 : ℝ≥0∞) ^ m) atTop :=
            Filter.liminf_le_liminf (Filter.Eventually.of_forall hCoverBound)
        _ = (2 : ℝ≥0∞) ^ m := liminf_const _
    -- Combine the two bounds with `μH[m] U = hConst m * ω`.
    have hEval : (Measure.hausdorffMeasure (m : ℝ) : Measure E) U = hConst m * ω := by
      rw [hHeq]; rfl
    rw [hEval] at hLower hUpper
    have hfinal : hConst m * ω = (2 : ℝ≥0∞) ^ m := le_antisymm hUpper hLower
    unfold HConstValueProp
    exact (ENNReal.eq_div_iff hω_ne0 hω_net).mpr (by rw [mul_comm]; exact hfinal)

end RobinCaps.Hausdorff

end
