import RobinCaps.Hausdorff.IsodiamIface

/-!
# Compactness of the Steiner symmetral (wave 13, `SteinerCompactProp`)

Main result: `steinerCompact_stc`, proving `SteinerCompactProp m` from `IsodiamIface`, i.e. for
every `m`, coordinate `i : Fin m` and compact `A ⊆ ℝ^m`, the Steiner symmetral `steinerSym i A` is
compact.

The proof follows the standard route:

* `updE` moves only the `i`-th coordinate, so `t ↦ updE x i t` is an isometric embedding of `ℝ`
  into `EuclideanSpace ℝ (Fin m)` for fixed `x`; this gives the basic algebraic/metric lemmas
  `updE_apply_stc`, `updE_updE_stc`, `updE_self_stc`, `dist_updE_of_eq_stc`, `dist_updE_le_stc`,
  `dist_updE_stc`, `coord_dist_le_stc`, `fiberE_updE_stc`, and the sequential continuity lemma
  `tendsto_updE_stc`.
* `isCompact_fiberE_stc` shows every fibre `fiberE i A x` is a compact subset of `ℝ` (closed as
  the preimage of the closed set `A` under an isometry, bounded because `A` is bounded).
* `volume_fiberE_le_diam_stc` bounds the fibre's volume by `diam A` (via `Real.volume_le_diam`
  and monotonicity of `EMetric.diam`).
* `isBounded_steinerSym_stc` uses the above to bound `steinerSym i A`.
* `isClosed_steinerSym_stc` proves sequential closedness: given `u n ∈ steinerSym i A` with
  `u n → x`, first extracts a convergent subsequence of witnesses `t n` (with `updE (u n) i (t n)
  ∈ A`) to show the fibre at `x` is nonempty, then an upper-semicontinuity-of-measure argument
  (via `tendsto_measure_cthickening_of_isCompact`) to pass the defining inequality
  `2 |u n i| ≤ volume (fiberE i A (u n))` to the limit.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal Topology

namespace RobinCaps.Hausdorff

variable {m : ℕ}

/-! ## Basic algebra of `updE` -/

theorem updE_apply_stc (x : EuclideanSpace ℝ (Fin m)) (i : Fin m) (t : ℝ) (j : Fin m) :
    updE x i t j = if j = i then t else x j := by
  simp only [updE, PiLp.toLp_apply, Function.update_apply]

theorem updE_apply_self_stc (x : EuclideanSpace ℝ (Fin m)) (i : Fin m) (t : ℝ) :
    updE x i t i = t := by
  simp [updE_apply_stc]

theorem updE_apply_ne_stc (x : EuclideanSpace ℝ (Fin m)) (i : Fin m) (t : ℝ) {j : Fin m}
    (hj : j ≠ i) : updE x i t j = x j := by
  simp [updE_apply_stc, hj]

theorem updE_updE_stc (x : EuclideanSpace ℝ (Fin m)) (i : Fin m) (s t : ℝ) :
    updE (updE x i s) i t = updE x i t := by
  ext j
  by_cases hj : j = i <;> simp [updE_apply_stc, hj]

theorem updE_self_stc (x : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    updE x i (x i) = x := by
  ext j
  by_cases hj : j = i <;> simp [updE_apply_stc, hj]

theorem fiberE_updE_stc (i : Fin m) (A : Set (EuclideanSpace ℝ (Fin m)))
    (x : EuclideanSpace ℝ (Fin m)) (s : ℝ) :
    fiberE i A (updE x i s) = fiberE i A x := by
  ext t
  simp [fiberE, updE_updE_stc]

/-! ## Metric lemmas -/

/-- Elementary helper: on `ℝ`, `a ≤ b` follows from `a ^ 2 ≤ b ^ 2` and nonnegativity. -/
theorem le_of_sq_le_sq_stc {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  have := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq ha, Real.sqrt_sq hb] at this

/-- `t ↦ updE x i t` is an isometric embedding of `ℝ` (fixed base point `x`). -/
theorem dist_updE_of_eq_stc (x : EuclideanSpace ℝ (Fin m)) (i : Fin m) (s t : ℝ) :
    dist (updE x i s) (updE x i t) = |s - t| := by
  have h : dist (updE x i s) (updE x i t) ^ 2 = (s - t) ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq, Finset.sum_eq_single i]
    · rw [updE_apply_self_stc, updE_apply_self_stc, Real.dist_eq, sq_abs]
    · intro j _ hj
      rw [updE_apply_ne_stc x i s hj, updE_apply_ne_stc x i t hj]
      simp
    · intro h
      exact absurd (Finset.mem_univ i) h
  have := congrArg Real.sqrt h
  rwa [Real.sqrt_sq dist_nonneg, Real.sqrt_sq_eq_abs] at this

/-- Distance from `x` to a single-coordinate move of `x`. -/
theorem dist_self_updE_stc (x : EuclideanSpace ℝ (Fin m)) (i : Fin m) (t : ℝ) :
    dist x (updE x i t) = |x i - t| := by
  have h : dist x (updE x i t) ^ 2 = (x i - t) ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq, Finset.sum_eq_single i]
    · rw [updE_apply_self_stc, Real.dist_eq, sq_abs]
    · intro j _ hj
      rw [updE_apply_ne_stc x i t hj, dist_self]
      simp
    · intro h
      exact absurd (Finset.mem_univ i) h
  have := congrArg Real.sqrt h
  rwa [Real.sqrt_sq dist_nonneg, Real.sqrt_sq_eq_abs] at this

/-- Moving only the `i`-th coordinate is `1`-Lipschitz in the base point. -/
theorem dist_updE_le_stc (x y : EuclideanSpace ℝ (Fin m)) (i : Fin m) (s : ℝ) :
    dist (updE x i s) (updE y i s) ≤ dist x y := by
  apply le_of_sq_le_sq_stc dist_nonneg dist_nonneg
  rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : j = i
  · subst hj
    rw [updE_apply_self_stc, updE_apply_self_stc, dist_self]
    have h0 : (0 : ℝ) ^ 2 = 0 := by norm_num
    rw [h0]
    exact sq_nonneg _
  · rw [updE_apply_ne_stc x i s hj, updE_apply_ne_stc y i s hj]

/-- Combined Lipschitz bound for `(x, t) ↦ updE x i t`. -/
theorem dist_updE_stc (x y : EuclideanSpace ℝ (Fin m)) (i : Fin m) (s t : ℝ) :
    dist (updE x i s) (updE y i t) ≤ dist x y + |s - t| := by
  refine (dist_triangle (updE x i s) (updE y i s) (updE y i t)).trans ?_
  rw [dist_updE_of_eq_stc y i s t]
  exact add_le_add (dist_updE_le_stc x y i s) le_rfl

/-- Sequential continuity of `(x, t) ↦ updE x i t`. -/
theorem tendsto_updE_stc {i : Fin m} {x : ℕ → EuclideanSpace ℝ (Fin m)}
    {x0 : EuclideanSpace ℝ (Fin m)} {t : ℕ → ℝ} {t0 : ℝ} (hx : Tendsto x atTop (𝓝 x0))
    (ht : Tendsto t atTop (𝓝 t0)) :
    Tendsto (fun n => updE (x n) i (t n)) atTop (𝓝 (updE x0 i t0)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hx' : Tendsto (fun n => dist (x n) x0) atTop (𝓝 0) := tendsto_iff_dist_tendsto_zero.mp hx
  have ht' : Tendsto (fun n => |t n - t0|) atTop (𝓝 0) := by
    have h := tendsto_iff_dist_tendsto_zero.mp ht
    simpa [Real.dist_eq] using h
  have hsum : Tendsto (fun n => dist (x n) x0 + |t n - t0|) atTop (𝓝 0) := by
    simpa using hx'.add ht'
  exact squeeze_zero (fun _ => dist_nonneg) (fun n => dist_updE_stc (x n) x0 i (t n) t0) hsum

/-- A coordinate projection is `1`-Lipschitz on `EuclideanSpace ℝ (Fin m)`. -/
theorem coord_dist_le_stc (x y : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    dist (x i) (y i) ≤ dist x y := by
  apply le_of_sq_le_sq_stc dist_nonneg dist_nonneg
  rw [EuclideanSpace.dist_sq_eq]
  exact Finset.single_le_sum (fun j _ => sq_nonneg (dist (x j) (y j))) (Finset.mem_univ i)

/-! ## Compactness and volume of the fibres -/

/-- Every fibre of a compact set is a compact subset of `ℝ`. -/
theorem isCompact_fiberE_stc (i : Fin m) (A : Set (EuclideanSpace ℝ (Fin m))) (hA : IsCompact A)
    (x : EuclideanSpace ℝ (Fin m)) : IsCompact (fiberE i A x) := by
  apply isCompact_of_isClosed_isBounded
  · have hiso : Isometry (fun t : ℝ => updE x i t) :=
      Isometry.of_dist_eq fun s t => dist_updE_of_eq_stc x i s t
    have hset : fiberE i A x = (fun t : ℝ => updE x i t) ⁻¹' A := rfl
    rw [hset]
    exact hA.isClosed.preimage hiso.continuous
  · rcases (fiberE i A x).eq_empty_or_nonempty with he | ⟨t0, ht0⟩
    · simp [he]
    · have hA0 : updE x i t0 ∈ A := ht0
      obtain ⟨R, hR⟩ := hA.isBounded.subset_closedBall (updE x i t0)
      refine (isBounded_closedBall (x := t0) (r := R)).subset ?_
      intro t ht
      have hmem : updE x i t ∈ A := ht
      have hd : dist (updE x i t) (updE x i t0) ≤ R := mem_closedBall.mp (hR hmem)
      rw [dist_updE_of_eq_stc] at hd
      exact mem_closedBall.mpr (by rw [Real.dist_eq]; exact hd)

/-- The volume of a fibre is bounded by the (extended) diameter of `A`. -/
theorem volume_fiberE_le_diam_stc (i : Fin m) (A : Set (EuclideanSpace ℝ (Fin m)))
    (x : EuclideanSpace ℝ (Fin m)) : volume (fiberE i A x) ≤ EMetric.diam A := by
  refine (Real.volume_le_diam _).trans (EMetric.diam_le ?_)
  intro s hs t ht
  have hs' : updE x i s ∈ A := hs
  have ht' : updE x i t ∈ A := ht
  have heq : edist s t = edist (updE x i s) (updE x i t) := by
    rw [edist_dist, edist_dist, Real.dist_eq, dist_updE_of_eq_stc]
  rw [heq]
  exact EMetric.edist_le_diam_of_mem hs' ht'

/-- Every coordinate of a point of `EuclideanSpace ℝ (Fin m)` is bounded by its norm. -/
theorem abs_apply_le_norm_stc (x : EuclideanSpace ℝ (Fin m)) (i : Fin m) : |x i| ≤ ‖x‖ := by
  have h := coord_dist_le_stc x 0 i
  simpa [Real.dist_eq, dist_eq_norm] using h

/-- `steinerSym i A` is bounded whenever `A` is compact. -/
theorem isBounded_steinerSym_stc (i : Fin m) (A : Set (EuclideanSpace ℝ (Fin m)))
    (hA : IsCompact A) : Bornology.IsBounded (steinerSym i A) := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨a0, ha0⟩
  · have he : steinerSym i (∅ : Set (EuclideanSpace ℝ (Fin m))) = ∅ := by
      ext x; simp [steinerSym, fiberE]
    simp [he]
  · obtain ⟨R, hR⟩ := hA.isBounded.subset_closedBall a0
    have hR0 : 0 ≤ R := dist_nonneg.trans (mem_closedBall.mp (hR ha0))
    refine (isBounded_closedBall (x := a0) (r := 4 * R + ‖a0‖)).subset ?_
    intro x hx
    obtain ⟨t, ht⟩ := hx.1
    have hmemt : updE x i t ∈ A := ht
    have hdRt : dist (updE x i t) a0 ≤ R := mem_closedBall.mp (hR hmemt)
    -- (1) bound |x i| ≤ 2 R via the volume/diam estimate on the fibre through `x`
    have hxi : |x i| ≤ 2 * R := by
      have hsub : fiberE i A x ⊆ Icc (t - 2 * R) (t + 2 * R) := by
        intro t' ht'
        have hmemt' : updE x i t' ∈ A := ht'
        have hd' : dist (updE x i t') a0 ≤ R := mem_closedBall.mp (hR hmemt')
        have htri : dist (updE x i t') (updE x i t) ≤ 2 * R := by
          calc dist (updE x i t') (updE x i t)
              ≤ dist (updE x i t') a0 + dist a0 (updE x i t) := dist_triangle _ _ _
            _ ≤ R + R := by rw [dist_comm a0 (updE x i t)]; linarith
            _ = 2 * R := by ring
        rw [dist_updE_of_eq_stc] at htri
        have habs := abs_le.mp htri
        exact ⟨by linarith [habs.1], by linarith [habs.2]⟩
      have hvol : volume (fiberE i A x) ≤ volume (Icc (t - 2 * R) (t + 2 * R)) :=
        measure_mono hsub
      have hvolIcc : volume (Icc (t - 2 * R) (t + 2 * R)) = ENNReal.ofReal (4 * R) := by
        rw [Real.volume_Icc]; ring_nf
      have hle : (volume (fiberE i A x)).toReal ≤ 4 * R := by
        have h1 : volume (fiberE i A x) ≤ ENNReal.ofReal (4 * R) := hvolIcc ▸ hvol
        have h2 : (volume (fiberE i A x)).toReal ≤ (ENNReal.ofReal (4 * R)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
        rwa [ENNReal.toReal_ofReal (by linarith)] at h2
      linarith [hx.2]
    -- (2) bound |t - a0 i| ≤ R via the coordinate-projection Lipschitz bound
    have hti : |t - a0 i| ≤ R := by
      have hc := coord_dist_le_stc (updE x i t) a0 i
      rw [updE_apply_self_stc] at hc
      calc |t - a0 i| = dist t (a0 i) := (Real.dist_eq t (a0 i)).symm
        _ ≤ dist (updE x i t) a0 := hc
        _ ≤ R := hdRt
    -- (3) combine via the triangle inequality
    have hai : |a0 i| ≤ ‖a0‖ := abs_apply_le_norm_stc a0 i
    have hxa0t : dist x (updE x i t) = |x i - t| := dist_self_updE_stc x i t
    have habs : |x i - t| ≤ 3 * R + ‖a0‖ := by
      rw [abs_le] at hxi hti hai ⊢
      constructor <;> linarith [hxi.1, hxi.2, hti.1, hti.2, hai.1, hai.2]
    have hfinal : dist x a0 ≤ 4 * R + ‖a0‖ := by
      have htri : dist x a0 ≤ dist x (updE x i t) + dist (updE x i t) a0 := dist_triangle _ _ _
      rw [hxa0t] at htri
      linarith
    exact mem_closedBall.mpr hfinal

/-! ## Closedness of the Steiner symmetral -/

theorem isClosed_steinerSym_stc (i : Fin m) (A : Set (EuclideanSpace ℝ (Fin m)))
    (hA : IsCompact A) : IsClosed (steinerSym i A) := by
  apply IsSeqClosed.isClosed
  intro u x hu hux
  rcases A.eq_empty_or_nonempty with rfl | ⟨a0, ha0⟩
  · exact absurd (hu 0).1 (by simp [fiberE])
  obtain ⟨R, hR⟩ := hA.isBounded.subset_closedBall a0
  -- witnesses `t n` with `updE (u n) i (t n) ∈ A`
  choose t ht using fun n => (hu n).1
  have htb : ∀ n, dist (t n) (a0 i) ≤ R := fun n => by
    have hc := coord_dist_le_stc (updE (u n) i (t n)) a0 i
    rw [updE_apply_self_stc] at hc
    exact hc.trans (mem_closedBall.mp (hR (ht n)))
  obtain ⟨s, -, φ, hφ, hφt⟩ :=
    tendsto_subseq_of_bounded (isBounded_closedBall (x := a0 i) (r := R))
      (fun n => mem_closedBall.mpr (htb n))
  have huφ : Tendsto (u ∘ φ) atTop (𝓝 x) := hux.comp hφ.tendsto_atTop
  have hconv : Tendsto (fun n => updE (u (φ n)) i (t (φ n))) atTop (𝓝 (updE x i s)) :=
    tendsto_updE_stc huφ hφt
  have hAlim : updE x i s ∈ A :=
    hA.isClosed.mem_of_tendsto hconv (Eventually.of_forall fun n => ht (φ n))
  have hFne : (fiberE i A x).Nonempty := ⟨s, hAlim⟩
  refine ⟨hFne, ?_⟩
  set F := fiberE i A x with hFdef
  have hFcpt : IsCompact F := isCompact_fiberE_stc i A hA x
  have hxin : Tendsto (fun n => (u n) i) atTop (𝓝 (x i)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ => dist_nonneg) (fun n => coord_dist_le_stc (u n) x i)
      (tendsto_iff_dist_tendsto_zero.mp hux)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  -- Step 1: find `r0 > 0` with `volume (cthickening r0 F) < volume F + ofReal ε`
  have hFvolNe : volume F ≠ ⊤ := hFcpt.measure_ne_top
  have hlt : volume F < volume F + ENNReal.ofReal ε :=
    ENNReal.lt_add_right hFvolNe (ne_of_gt (ENNReal.ofReal_pos.mpr hε))
  have hnhd : Set.Iio (volume F + ENNReal.ofReal ε) ∈ 𝓝 (volume F) := isOpen_Iio.mem_nhds hlt
  have hevent : ∀ᶠ r in 𝓝 (0 : ℝ), volume (cthickening r F) < volume F + ENNReal.ofReal ε :=
    (tendsto_measure_cthickening_of_isCompact hFcpt).eventually_mem hnhd
  obtain ⟨δ, hδ0, hδ⟩ := Metric.eventually_nhds_iff.mp hevent
  set r0 : ℝ := δ / 2 with hr0def
  have hr0pos : 0 < r0 := by positivity
  have hr0 : volume (cthickening r0 F) < volume F + ENNReal.ofReal ε :=
    hδ (show dist r0 (0 : ℝ) < δ by rw [Real.dist_eq, sub_zero, abs_of_pos hr0pos]; linarith)
  -- Step 2: eventually `fiberE i A (u n) ⊆ cthickening r0 F`
  have hsub_ev : ∃ N, ∀ n ≥ N, fiberE i A (u n) ⊆ cthickening r0 F := by
    by_contra hcon
    push_neg at hcon
    have hfreq : ∃ᶠ n in atTop, ∃ s' ∈ fiberE i A (u n), s' ∉ cthickening r0 F := by
      rw [frequently_atTop']
      intro N
      obtain ⟨n, hnN, hne⟩ := hcon (N + 1)
      rw [Set.not_subset] at hne
      exact ⟨n, by omega, hne⟩
    obtain ⟨ψ, hψ, hψp⟩ := extraction_of_frequently_atTop hfreq
    choose w hw1 hw2 using hψp
    have hwb : ∀ n, dist (w n) (a0 i) ≤ R := fun n => by
      have hc := coord_dist_le_stc (updE (u (ψ n)) i (w n)) a0 i
      rw [updE_apply_self_stc] at hc
      have hmem : updE (u (ψ n)) i (w n) ∈ A := hw1 n
      exact hc.trans (mem_closedBall.mp (hR hmem))
    obtain ⟨winf, -, χ, hχ, hχw⟩ :=
      tendsto_subseq_of_bounded (isBounded_closedBall (x := a0 i) (r := R))
        (fun n => mem_closedBall.mpr (hwb n))
    have huψχ : Tendsto (fun n => u (ψ (χ n))) atTop (𝓝 x) :=
      hux.comp (hψ.comp hχ).tendsto_atTop
    have hconv2 : Tendsto (fun n => updE (u (ψ (χ n))) i (w (χ n))) atTop (𝓝 (updE x i winf)) :=
      tendsto_updE_stc huψχ hχw
    have hAlim2 : updE x i winf ∈ A :=
      hA.isClosed.mem_of_tendsto hconv2 (Eventually.of_forall fun n => hw1 (χ n))
    have hwinfF : winf ∈ F := hAlim2
    have hcontI : Continuous (fun y => EMetric.infEdist y F) := EMetric.continuous_infEdist
    have htendI : Tendsto (fun n => EMetric.infEdist (w (χ n)) F) atTop
        (𝓝 (EMetric.infEdist winf F)) := (hcontI.tendsto winf).comp hχw
    have hgeq : ∀ n, ENNReal.ofReal r0 ≤ EMetric.infEdist (w (χ n)) F := fun n => by
      have hnot := hw2 (χ n)
      rw [mem_cthickening_iff] at hnot
      exact le_of_not_ge hnot
    have hle : ENNReal.ofReal r0 ≤ EMetric.infEdist winf F := ge_of_tendsto' htendI hgeq
    rw [EMetric.infEdist_zero_of_mem hwinfF] at hle
    exact absurd hle (not_le.mpr (ENNReal.ofReal_pos.mpr hr0pos))
  obtain ⟨N, hN⟩ := hsub_ev
  have hvol_lt : ∀ n ≥ N, volume (fiberE i A (u n)) < volume F + ENNReal.ofReal ε := fun n hn =>
    lt_of_le_of_lt (measure_mono (hN n hn)) hr0
  -- Step 3: pass the defining Steiner inequality to the limit
  have hstep : ∀ n ≥ N, 2 * |(u n) i| ≤ (volume F).toReal + ε := fun n hn => by
    have h1 := (hu n).2
    have hfin : volume F + ENNReal.ofReal ε ≠ ⊤ := by
      simp [hFvolNe]
    have h2 := ENNReal.toReal_mono hfin (hvol_lt n hn).le
    rw [ENNReal.toReal_add hFvolNe ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hε.le] at h2
    linarith
  have hfin_tendsto : Tendsto (fun n => 2 * |(u n) i|) atTop (𝓝 (2 * |x i|)) :=
    (hxin.abs).const_mul 2
  exact le_of_tendsto hfin_tendsto (eventually_atTop.mpr ⟨N, hstep⟩)

/-! ## Main theorem -/

/-- The Steiner symmetral of a compact set is compact. -/
theorem steinerCompact_stc (m : ℕ) : SteinerCompactProp m := fun i A hA =>
  isCompact_of_isClosed_isBounded (isClosed_steinerSym_stc i A hA) (isBounded_steinerSym_stc i A hA)

end RobinCaps.Hausdorff

end
