import RobinCaps.Compact.ConvexRellichIface

/-!
# Rellich–Kondrachov on a bounded convex open set (wave 12)

This file proves the Rellich–Kondrachov compactness theorem on a general bounded convex open
set `Ω`, taking the approximation estimate `ApproxEstimateCvx Ω r₀ ρ₀` (proved elsewhere from
`SmoothConvSetEst`/`SmoothDilateSetEst`, see `Compact/ConvexRellichIface.lean`) as a hypothesis.
It is the direct transcription of `Compact/Rellich.lean` (Rellich–Kondrachov on a ball) to a
general convex domain, with `approx` replaced by `approxCvx` throughout.

* `totallyBounded_range_of_dist_le_rcx`: an abstract metric-space lemma — if `dist (a k) (a l) ≤
  dist (b k) (b l)` for all `k, l` and `Set.range b` is totally bounded, so is `Set.range a`.
  Proved via `totallyBounded_of_finite_discretization`: an `(ε/2)`-net of `range b` gives, for
  each `k`, a nearby net point; indices sharing the same net point have `b`-distance `< ε`,
  hence `a`-distance `< ε` too.
* `integral_extCd_sq_rcx`, `mass_dilateWideCd_rcx`: the convex-domain analogues of
  `integral_ext_sq` and `mass_dilate` (`Compact/Basic.lean`, `Compact/Dilation.lean`): the
  squared `L²(ℝⁿ)` norm of the zero-extension is the mass, and the mass scales by `lam⁻ⁿ` under
  `dilateWideCd`.
* `totallyBounded_range_rcx`: the `L²(Ω)` classes of an `H¹(Ω)`-bounded sequence have totally
  bounded range.  As in `totallyBounded_range_toL2`, for `η > 0` the smooth approximants
  `approxCvx (u k) lam ε` are uniformly `η`-close to `u k` in `L²(Ω)` (`ApproxEstimateCvx`), and
  — being uniformly bounded and uniformly Lipschitz — have totally bounded range in
  `L²(ball 0 R')` for `R'` with `Ω ⊆ ball 0 R'` (Arzelà–Ascoli, `ArzelaAscoli.lean`); this is
  transferred to `L²(Ω)` via `totallyBounded_range_of_dist_le_rcx`, since the `L²(Ω)` distance
  of two functions is at most their `L²(ball 0 R')` distance.
* `rellichL2_convex_rcx`, `rellich_convex_rcx`: the Rellich–Kondrachov theorem on `Ω`, in the
  `L²`-limit form `RellichEmbeddingL2 Ω` and in the form of the target
  `RobinCaps.Sobolev.Weak.RellichEmbedding Ω`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

open MeasureTheory Metric Set Filter
open scoped Convolution ContDiff ENNReal Topology

namespace RobinCaps.Compact

open RobinCaps.Sobolev.Weak
open RobinCaps.Sobolev (extCd dilatedDomainCd dilateWideCd dilateWideCd_toFun memLp_extCd
  isOpen_dilatedDomain_cd)

variable {n : ℕ}

/-- The ambient Euclidean space `ℝⁿ`. -/
local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ## An abstract total-boundedness transfer -/

/-- **Domination transfers total boundedness.** If `dist (a k) (a l) ≤ dist (b k) (b l)` for
every `k, l : ℕ`, and `Set.range b` is totally bounded, then so is `Set.range a`. -/
theorem totallyBounded_range_of_dist_le_rcx {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] (a : ℕ → X) (b : ℕ → Y)
    (h : ∀ k l, dist (a k) (a l) ≤ dist (b k) (b l)) (hb : TotallyBounded (Set.range b)) :
    TotallyBounded (Set.range a) := by
  classical
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨t, ht_fin, ht_cover⟩ := Metric.totallyBounded_iff.1 hb (ε / 2) (by linarith)
  set center : Y → X := fun y => a (if hy : ∃ k, dist (b k) y < ε / 2 then hy.choose else 0)
    with hcenterdef
  refine ⟨center '' t, ht_fin.image _, ?_⟩
  rintro - ⟨k, rfl⟩
  obtain ⟨y, hyt, hy_ball⟩ := Set.mem_iUnion₂.1 (ht_cover (Set.mem_range_self k))
  have hy_ball' : dist (b k) y < ε / 2 := hy_ball
  have hy_ex : ∃ k', dist (b k') y < ε / 2 := ⟨k, hy_ball'⟩
  refine Set.mem_iUnion₂.2 ⟨center y, Set.mem_image_of_mem _ hyt, ?_⟩
  show dist (a k) (a (if hy2 : ∃ k', dist (b k') y < ε / 2 then hy2.choose else 0)) < ε
  rw [dif_pos hy_ex]
  set k' := hy_ex.choose with hk'def
  have hk' : dist (b k') y < ε / 2 := hy_ex.choose_spec
  have hbb : dist (b k) (b k') < ε := by
    have h2 : dist y (b k') < ε / 2 := by rw [dist_comm]; exact hk'
    calc dist (b k) (b k') ≤ dist (b k) y + dist y (b k') := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := by linarith
      _ = ε := by ring
  calc dist (a k) (a k') ≤ dist (b k) (b k') := h k k'
    _ < ε := hbb

/-! ## `extCd` and `dilateWideCd`: the squared `L²` norm and mass scaling -/

/-- `∫ (extCd u)² = mass u`, the convex-domain analogue of `integral_ext_sq`. -/
theorem integral_extCd_sq_rcx {Ω : Set E} (hΩ : MeasurableSet Ω) (u : H1 Ω) :
    ∫ x, extCd u x ^ 2 = mass u := by
  unfold mass extCd
  rw [← integral_indicator hΩ]
  congr 1
  funext x
  by_cases hx : x ∈ Ω
  · simp [indicator_of_mem hx]
  · simp [indicator_of_notMem hx]

/-- The mass scales by `lam⁻ⁿ` under `dilateWideCd`, the convex-domain analogue of
`mass_dilate`. -/
theorem mass_dilateWideCd_rcx {Ω : Set E} (hΩ : MeasurableSet Ω) (u : H1 Ω) {lam : ℝ}
    (hlam0 : 0 < lam) : mass (dilateWideCd hΩ u hlam0) = lam⁻¹ ^ n * mass u := by
  have h1 : mass (dilateWideCd hΩ u hlam0)
      = ∫ x in dilatedDomainCd Ω lam, u.toFun (lam • x) ^ 2 := by
    unfold mass
    rw [dilateWideCd_toFun]
  rw [h1]
  have h2 := setIntegral_comp_smul hlam0 hΩ (fun y => u.toFun y ^ 2)
  show (∫ x in (fun x : E => lam • x) ⁻¹' Ω, u.toFun (lam • x) ^ 2) = lam⁻¹ ^ n * mass u
  rw [h2, inv_pow]
  rfl

/-! ## Total boundedness of an `H¹(Ω)`-bounded sequence in `L²(Ω)` -/

/-- The `L²(Ω)` classes of an `H¹(Ω)`-bounded sequence have totally bounded range. -/
theorem totallyBounded_range_rcx {Ω : Set E} (hconv : Convex ℝ Ω) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) (h0 : (0 : E) ∈ Ω)
    (hA : ∀ r₀ ρ₀ : ℝ, 0 < r₀ → Metric.ball (0 : E) r₀ ⊆ Ω → 0 ≤ ρ₀ →
      (∀ x ∈ Ω, ‖x‖ ≤ ρ₀) → ApproxEstimateCvx Ω r₀ ρ₀)
    (u : ℕ → H1 Ω) {M : ℝ} (hM : ∀ k, dirichlet (u k) + mass (u k) ≤ M) :
    TotallyBounded (Set.range fun k => (u k).memL2.toLp (u k).toFun) := by
  -- geometry: `ball 0 r₀ ⊆ Ω ⊆ ball 0 R'`
  obtain ⟨r₀, hr₀, hr₀sub⟩ := Metric.isOpen_iff.mp hopen 0 h0
  obtain ⟨ρ₀, hρ₀pos, hρ₀⟩ := hbdd.exists_pos_norm_le
  have hΩmeas : MeasurableSet Ω := hopen.measurableSet
  set R' : ℝ := ρ₀ + 1 with hR'def
  have hΩR' : Ω ⊆ ball (0 : E) R' := by
    intro x hx
    rw [mem_ball, dist_zero_right]
    have := hρ₀ x hx
    linarith
  have hApprox : ApproxEstimateCvx Ω r₀ ρ₀ := hA r₀ ρ₀ hr₀ hr₀sub hρ₀pos.le hρ₀
  have hM0 : 0 ≤ M :=
    le_trans (add_nonneg (dirichlet_nonneg (u 0)) (mass_nonneg (u 0))) (hM 0)
  have hdir : ∀ k, dirichlet (u k) ≤ M := fun k =>
    le_trans (le_add_of_nonneg_right (mass_nonneg (u k))) (hM k)
  have hmass : ∀ k, mass (u k) ≤ M := fun k =>
    le_trans (le_add_of_nonneg_left (dirichlet_nonneg (u k))) (hM k)
  refine totallyBounded_range_of_approx _ fun η hη => ?_
  -- choose the parameters `lam, ε`
  set c1 : ℝ := 1 / 4 + ρ₀ / (2 * r₀) with hc1def
  have hc1nn : 0 ≤ c1 := by positivity
  obtain ⟨t, ht0, htr₀, htη⟩ :=
    exists_small_param (c := 2 ^ (n + 1) * M * c1 ^ 2) hr₀
      (by positivity) hη
  set lam : ℝ := 1 - t / (2 * r₀) with hlamdef
  set ε : ℝ := t / 4 with hεdef
  have h2r₀ : (0 : ℝ) < 2 * r₀ := by positivity
  have htq : t / (2 * r₀) ≤ 1 / 2 := by
    rw [div_le_iff₀ h2r₀]; linarith
  have htq0 : 0 < t / (2 * r₀) := by positivity
  have hlam_half : 1 / 2 ≤ lam := by rw [hlamdef]; linarith
  have hlam1 : lam < 1 := by rw [hlamdef]; linarith
  have hlam0 : 0 < lam := by linarith
  have hε0 : 0 < ε := by rw [hεdef]; linarith
  have hone_sub_lam : 1 - lam = t / (2 * r₀) := by rw [hlamdef]; ring
  have hcalc : (1 - lam) * r₀ = t / 2 := by
    rw [hone_sub_lam]
    field_simp
  have hε' : ε < (1 - lam) * r₀ := by rw [hεdef, hcalc]; linarith
  have hsum : ε + (1 - lam) * ρ₀ = t * c1 := by
    rw [hεdef, hone_sub_lam, hc1def]; ring
  -- the approximants
  have hρmol : IsMollifier ε (mollifier (n := n) ε) := isMollifier_mollifier hε0
  have hw : ∀ k, MemLp (extCd (dilateWideCd hΩmeas (u k) hlam0)) 2 volume := fun k =>
    memLp_extCd _ (isOpen_dilatedDomain_cd hopen lam).measurableSet
  have hg_memLp : ∀ k, MemLp (approxCvx (u k) lam ε) 2 volume := fun k => by
    rw [approxCvx_eq_extCd hΩmeas (u k) hlam0]
    exact memLp_conv hρmol (hw k)
  have hgball : ∀ k, MemLp (approxCvx (u k) lam ε) 2 (volume.restrict (ball (0 : E) R')) :=
    fun k => (hg_memLp k).restrict _
  have hgΩ : ∀ k, MemLp (approxCvx (u k) lam ε) 2 (volume.restrict Ω) := fun k =>
    (hg_memLp k).restrict _
  have hg_sq : ∀ k, ∫ t, extCd (dilateWideCd hΩmeas (u k) hlam0) t ^ 2 ≤ 2 ^ n * M := by
    intro k
    rw [integral_extCd_sq_rcx (isOpen_dilatedDomain_cd hopen lam).measurableSet,
      mass_dilateWideCd_rcx hΩmeas (u k) hlam0]
    calc lam⁻¹ ^ n * mass (u k) ≤ 2 ^ n * mass (u k) :=
          mul_le_mul_of_nonneg_right (inv_pow_le_two_pow hlam_half) (mass_nonneg _)
      _ ≤ 2 ^ n * M := mul_le_mul_of_nonneg_left (hmass k) (by positivity)
  have hg_sqrt : ∀ k, Real.sqrt (∫ t, extCd (dilateWideCd hΩmeas (u k) hlam0) t ^ 2)
      ≤ Real.sqrt (2 ^ n * M) := fun k => Real.sqrt_le_sqrt (hg_sq k)
  refine ⟨fun k => (hgΩ k).toLp (approxCvx (u k) lam ε), ?_, fun k => ?_⟩
  · -- total boundedness via Arzelà–Ascoli, transferred from `ball 0 R'` to `Ω`
    refine totallyBounded_range_of_dist_le_rcx (fun k => (hgΩ k).toLp (approxCvx (u k) lam ε))
      (fun k => (hgball k).toLp (approxCvx (u k) lam ε)) ?_ ?_
    · intro k l
      have hsq : dist ((hgΩ k).toLp (approxCvx (u k) lam ε))
          ((hgΩ l).toLp (approxCvx (u l) lam ε)) ^ 2
          ≤ dist ((hgball k).toLp (approxCvx (u k) lam ε))
              ((hgball l).toLp (approxCvx (u l) lam ε)) ^ 2 := by
        rw [dist_toLp_sq_measure (hgΩ k) (hgΩ l), dist_toLp_sq_measure (hgball k) (hgball l)]
        refine setIntegral_mono_set ?_ (Eventually.of_forall fun x => sq_nonneg _)
          hΩR'.eventuallyLE
        exact (((hg_memLp k).sub (hg_memLp l)).integrable_sq).integrableOn
      have h1 := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq dist_nonneg, Real.sqrt_sq dist_nonneg] at h1
    · refine totallyBounded_range_toLp_of_lipschitz (fun k => approxCvx (u k) lam ε)
        (A := Real.sqrt (∫ t, mollifier (n := n) ε t ^ 2) * Real.sqrt (2 ^ n * M))
        (L := Real.toNNReal
          (Real.sqrt (∫ t, ‖fderiv ℝ (mollifier (n := n) ε) t‖ ^ 2) * Real.sqrt (2 ^ n * M)))
        (fun k x => ?_) (fun k => ?_) hgball
      · dsimp only
        rw [approxCvx_eq_extCd hΩmeas (u k) hlam0]
        calc |(mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
              extCd (dilateWideCd hΩmeas (u k) hlam0)) x|
            ≤ Real.sqrt (∫ t, mollifier (n := n) ε t ^ 2)
                * Real.sqrt (∫ t, extCd (dilateWideCd hΩmeas (u k) hlam0) t ^ 2) :=
              abs_conv_le_sqrt hρmol (hw k) x
          _ ≤ Real.sqrt (∫ t, mollifier (n := n) ε t ^ 2) * Real.sqrt (2 ^ n * M) :=
              mul_le_mul_of_nonneg_left (hg_sqrt k) (Real.sqrt_nonneg _)
      · dsimp only
        rw [approxCvx_eq_extCd hΩmeas (u k) hlam0]
        refine (lipschitzWith_conv hρmol (hw k)).weaken ?_
        exact Real.toNNReal_le_toNNReal
          (mul_le_mul_of_nonneg_left (hg_sqrt k) (Real.sqrt_nonneg _))
  · -- closeness
    have hsq : dist ((u k).memL2.toLp (u k).toFun) ((hgΩ k).toLp (approxCvx (u k) lam ε)) ^ 2
        ≤ η ^ 2 := by
      rw [dist_comm, dist_toLp_sq_measure (hgΩ k) (u k).memL2]
      calc ∫ x in Ω, (approxCvx (u k) lam ε x - (u k).toFun x) ^ 2
          ≤ 2 ^ (n + 1) * (ε + (1 - lam) * ρ₀) ^ 2 * dirichlet (u k) :=
            hApprox (u k) lam ε hlam_half hlam1 hε0 hε'
        _ = 2 ^ (n + 1) * t ^ 2 * c1 ^ 2 * dirichlet (u k) := by rw [hsum]; ring
        _ ≤ 2 ^ (n + 1) * t ^ 2 * c1 ^ 2 * M :=
            mul_le_mul_of_nonneg_left (hdir k) (by positivity)
        _ = 2 ^ (n + 1) * M * c1 ^ 2 * t ^ 2 := by ring
        _ ≤ η ^ 2 := htη
    exact (pow_le_pow_iff_left₀ dist_nonneg hη.le two_ne_zero).1 hsq

/-! ## Rellich–Kondrachov on a bounded convex open set -/

/-- **Rellich–Kondrachov on a bounded convex open set**, `L²`-limit form. -/
theorem rellichL2_convex_rcx {Ω : Set E} (hconv : Convex ℝ Ω) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) (h0 : (0 : E) ∈ Ω)
    (hA : ∀ r₀ ρ₀ : ℝ, 0 < r₀ → Metric.ball (0 : E) r₀ ⊆ Ω → 0 ≤ ρ₀ →
      (∀ x ∈ Ω, ‖x‖ ≤ ρ₀) → ApproxEstimateCvx Ω r₀ ρ₀) :
    RellichEmbeddingL2 Ω := by
  intro u hu
  obtain ⟨M, hM⟩ := hu
  obtain ⟨ν, a, hν, ha⟩ :=
    exists_subseq_tendsto_of_totallyBounded (fun k => (u k).memL2.toLp (u k).toFun)
      (totallyBounded_range_rcx hconv hopen hbdd h0 hA u hM)
  refine ⟨ν, (a : E → ℝ), hν, Lp.memLp a, ?_⟩
  have h1 : Tendsto (fun k => dist ((u (ν k)).memL2.toLp (u (ν k)).toFun) a) atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.1 ha
  have h2 : Tendsto (fun k => dist ((u (ν k)).memL2.toLp (u (ν k)).toFun) a ^ 2) atTop (𝓝 0) := by
    simpa using h1.pow 2
  refine h2.congr fun k => ?_
  exact (dist_toLp_coe_sq_gen (u (ν k)).memL2 a).trans integral_norm_sub_sq_eq

/-- **Rellich–Kondrachov on a bounded convex open set**, in the form of the target
`Weak.RellichEmbedding`. -/
theorem rellich_convex_rcx {Ω : Set E} (hconv : Convex ℝ Ω) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) (h0 : (0 : E) ∈ Ω)
    (hA : ∀ r₀ ρ₀ : ℝ, 0 < r₀ → Metric.ball (0 : E) r₀ ⊆ Ω → 0 ≤ ρ₀ →
      (∀ x ∈ Ω, ‖x‖ ≤ ρ₀) → ApproxEstimateCvx Ω r₀ ρ₀) :
    RobinCaps.Sobolev.Weak.RellichEmbedding Ω := by
  intro u hu
  obtain ⟨ν, v, hν, _, htendsto⟩ := rellichL2_convex_rcx hconv hopen hbdd h0 hA u hu
  exact ⟨ν, v, hν, htendsto⟩

end RobinCaps.Compact

end
