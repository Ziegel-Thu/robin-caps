import Mathlib
import RobinCaps.Cap.Basic
import RobinCaps.Cap.Concave
import RobinCaps.Cap.Append
import RobinCaps.Domain.ThinConvex
import RobinCaps.ThinDomain.TrialBound
import RobinCaps.ThinDomain.Rescale

/-!
# Elementary geometry of the cap body `C.body`

Basic geometric facts about the body of an admissible end cap `C : Cap m` that are not already
recorded elsewhere: a linear lower bound on the profile obtained from concavity and the entrance
value, openness / convexity / boundedness of the body, an explicit cone of points near the
entrance that lie in the body, and the translated body `bodyShift_cg` (moved so that the origin
becomes an interior point), together with its basic properties.

All new declarations carry the suffix `_cg`.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace RobinCaps.Cap

variable {m : ℕ}

/-- `0 ≤ θ(0)`: the stored `θ(0)` is the left limit of a positive function. -/
theorem theta_zero_nonneg_cg (C : Cap m) : 0 ≤ C.θ 0 := by
  have hK0 : (-C.K : ℝ) < 0 := by linarith [C.hK]
  exact ge_of_tendsto C.θ_terminal
    (Filter.eventually_of_mem (Ioo_mem_nhdsLT hK0) fun s hs => (C.θ_pos s hs).le)

/-- **The linear lower bound `θ(s) ≥ −s/K` on `(−K,0)`**: by concavity the profile lies above
the chord from `(−K, 1)` to `(0, θ(0))`, and `θ(0) ≥ 0`. -/
theorem theta_ge_linear_cg (C : Cap m) {s : ℝ} (hs : s ∈ Set.Ioo (-C.K) 0) :
    -s / C.K ≤ C.θ s := by
  set μ : ℝ → ℝ := fun y => (y - s) / (y + C.K) with hμdef
  have hKne : C.K ≠ 0 := C.hK.ne'
  have hcontAt : ContinuousAt μ (0 : ℝ) := by
    have hf : Continuous (fun y : ℝ => y - s) := by fun_prop
    have hg : Continuous (fun y : ℝ => y + C.K) := by fun_prop
    have hg0 : (0 : ℝ) + C.K ≠ 0 := by simpa using hKne
    exact hf.continuousAt.div hg.continuousAt hg0
  have hval : μ 0 = -s / C.K := by simp only [hμdef]; ring
  have hlim : Tendsto μ (𝓝[<] (0 : ℝ)) (𝓝 (-s / C.K)) := by
    have h := hcontAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio (0 : ℝ)))
    rwa [hval] at h
  have hmem : Set.Ioo s (0 : ℝ) ∈ 𝓝[<] (0 : ℝ) := Ioo_mem_nhdsLT hs.2
  have hbound : ∀ᶠ y in 𝓝[<] (0 : ℝ), μ y ≤ C.θ s := by
    filter_upwards [hmem] with y hy
    have hpy : s ≤ y := hy.1.le
    have hyneg : y < 0 := hy.2
    have hyK : (0 : ℝ) < y + C.K := by have := hs.1; linarith [hy.1]
    have hyKne : y + C.K ≠ 0 := hyK.ne'
    have hcomb : μ y * (-C.K) + (1 - μ y) * y = s := by
      simp only [hμdef]
      field_simp
      ring
    have hj := appendθ_junction C hs.1 hpy hyneg hcomb
    have hyI : y ∈ Set.Ioo (-C.K) 0 := ⟨lt_of_lt_of_le hs.1 hpy, hyneg⟩
    have hθy : 0 < C.θ y := C.θ_pos y hyI
    have hμle1 : (0 : ℝ) ≤ 1 - μ y := by
      have hval : μ y = (y - s) / (y + C.K) := rfl
      rw [hval, sub_nonneg, div_le_one hyK]
      linarith [hs.1]
    have hnn : (0 : ℝ) ≤ (1 - μ y) * C.θ y := mul_nonneg hμle1 hθy.le
    linarith [hj]
  exact le_of_tendsto hlim hbound

/-- The body of a cap is open. -/
theorem isOpen_body_cg (C : Cap m) : IsOpen C.body := by
  rw [isOpen_iff_mem_nhds]
  rintro p ⟨h1, h2, h3⟩
  have hIoo : Set.Ioo (-C.K) 0 ∈ 𝓝 p.1 := Ioo_mem_nhds h1 h2
  have hθcont : ContinuousAt C.θ p.1 := (Concave.continuousOn_Ioo C).continuousAt hIoo
  have hθfst : ContinuousAt (fun q : CapSpace m => C.θ q.1) p := hθcont.comp continuousAt_fst
  have hnorm : ContinuousAt (fun q : CapSpace m => ‖q.2‖) p := continuous_snd.norm.continuousAt
  have hpair : ContinuousAt (fun q : CapSpace m => (C.θ q.1, ‖q.2‖)) p := hθfst.prodMk hnorm
  have hopenlt : IsOpen {q : ℝ × ℝ | q.2 < q.1} := isOpen_lt continuous_snd continuous_fst
  have hmemlt : (C.θ p.1, ‖p.2‖) ∈ {q : ℝ × ℝ | q.2 < q.1} := h3
  have hpre1 : (fun q : CapSpace m => q.1) ⁻¹' Set.Ioo (-C.K) 0 ∈ 𝓝 p :=
    continuousAt_fst.preimage_mem_nhds hIoo
  have hpre2 : (fun q : CapSpace m => (C.θ q.1, ‖q.2‖)) ⁻¹' {q : ℝ × ℝ | q.2 < q.1} ∈ 𝓝 p :=
    hpair.preimage_mem_nhds (hopenlt.mem_nhds hmemlt)
  refine Filter.mem_of_superset (Filter.inter_mem hpre1 hpre2) ?_
  rintro q ⟨hq1, hq2⟩
  exact ⟨hq1.1, hq1.2, hq2⟩

/-- The body of a cap is convex. -/
theorem convex_body_cg (C : Cap m) : Convex ℝ C.body := by
  have heq : C.body = {p : CapSpace m | p.1 ∈ Set.Ioo (-C.K) 0 ∧ ‖p.2‖ < C.θ p.1} := by
    ext p
    simp only [body, Set.mem_setOf_eq, Set.mem_Ioo]
    tauto
  rw [heq]
  exact RobinCaps.Domain.convex_of_concave_radius (convex_Ioo _ _) C.θ_concave

/-- The body of a cap is bounded. -/
theorem isBounded_body_cg (C : Cap m) : Bornology.IsBounded C.body :=
  (Bornology.IsBounded.prod (Metric.isBounded_Ioo (-C.K) 0) Metric.isBounded_ball).subset
    (RobinCaps.ThinDomain.body_subset_cyl C)

/-- The centre point of the cap. -/
theorem center_mem_body_cg (C : Cap m) :
    ((-C.K / 2 : ℝ), (0 : EuclideanSpace ℝ (Fin m))) ∈ C.body := by
  have hK := C.hK
  refine ⟨by linarith, by linarith, ?_⟩
  simp only [norm_zero]
  exact C.θ_pos (-C.K / 2) ⟨by linarith, by linarith⟩

/-- **The cone over the entrance disk.**  For `‖z‖ < 1` and `0 ≤ λ < 1`, the point on the
segment from the entrance point `(−K, z)` to the centre `(−K/2, 0)` at parameter `λ` lies in
the cap body. -/
theorem cone_mem_body_cg (C : Cap m) {z : EuclideanSpace ℝ (Fin m)} (hz : ‖z‖ < 1)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    ((-C.K + lam * C.K / 2 : ℝ), (1 - lam) • z) ∈ C.body := by
  have hK := C.hK
  have hs1 : -C.K < -C.K + lam * C.K / 2 := by nlinarith
  have hs2 : -C.K + lam * C.K / 2 < 0 := by nlinarith
  have hsI : (-C.K + lam * C.K / 2 : ℝ) ∈ Set.Ioo (-C.K) 0 := ⟨hs1, hs2⟩
  have hKne : C.K ≠ 0 := hK.ne'
  have hnorm : ‖(1 - lam) • z‖ = (1 - lam) * ‖z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - lam)]
  have hlin : -(-C.K + lam * C.K / 2) / C.K ≤ C.θ (-C.K + lam * C.K / 2) :=
    theta_ge_linear_cg C hsI
  have hseq : -(-C.K + lam * C.K / 2) / C.K = 1 - lam / 2 := by field_simp; ring
  refine ⟨hs1, hs2, ?_⟩
  rw [hnorm]
  have hstep1 : (1 - lam) * ‖z‖ < 1 - lam := by
    have h := mul_lt_mul_of_pos_left hz (show (0 : ℝ) < 1 - lam by linarith)
    simpa using h
  have hstep2 : (1 : ℝ) - lam ≤ 1 - lam / 2 := by linarith
  calc (1 - lam) * ‖z‖ < 1 - lam := hstep1
    _ ≤ 1 - lam / 2 := hstep2
    _ = -(-C.K + lam * C.K / 2) / C.K := hseq.symm
    _ ≤ C.θ (-C.K + lam * C.K / 2) := hlin

/-- The transverse slice at the axial level `−K + λK/2` contains the ball of radius `1 − λ`. -/
theorem ball_subset_slice_cg (C : Cap m) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1)
    {w : EuclideanSpace ℝ (Fin m)} (hw : ‖w‖ < 1 - lam) :
    ((-C.K + lam * C.K / 2 : ℝ), w) ∈ C.body := by
  have hK := C.hK
  have hs1 : -C.K < -C.K + lam * C.K / 2 := by nlinarith
  have hs2 : -C.K + lam * C.K / 2 < 0 := by nlinarith
  have hsI : (-C.K + lam * C.K / 2 : ℝ) ∈ Set.Ioo (-C.K) 0 := ⟨hs1, hs2⟩
  have hKne : C.K ≠ 0 := hK.ne'
  have hlin : -(-C.K + lam * C.K / 2) / C.K ≤ C.θ (-C.K + lam * C.K / 2) :=
    theta_ge_linear_cg C hsI
  have hseq : -(-C.K + lam * C.K / 2) / C.K = 1 - lam / 2 := by field_simp; ring
  refine ⟨hs1, hs2, ?_⟩
  have hstep2 : (1 : ℝ) - lam ≤ 1 - lam / 2 := by linarith
  calc ‖w‖ < 1 - lam := hw
    _ ≤ 1 - lam / 2 := hstep2
    _ = -(-C.K + lam * C.K / 2) / C.K := hseq.symm
    _ ≤ C.θ (-C.K + lam * C.K / 2) := hlin

/-- The translated cap body, moved so that the origin is an interior point: the image of
`C.body` under `p ↦ (p.1 + C.K/2, p.2)`. -/
def bodyShift_cg (C : Cap m) : Set (CapSpace m) :=
  (RobinCaps.ThinDomain.affP (-C.K / 2) 1 1) ⁻¹' C.body

theorem bodyShift_eq_cg (C : Cap m) :
    bodyShift_cg C =
      {p : CapSpace m | -C.K / 2 < p.1 ∧ p.1 < C.K / 2 ∧ ‖p.2‖ < C.θ (p.1 - C.K / 2)} := by
  have harg : ∀ p : CapSpace m, (-C.K / 2 + 1 * 1 * p.1 : ℝ) = p.1 - C.K / 2 := fun p => by ring
  ext p
  simp only [bodyShift_cg, Set.mem_preimage, body, Set.mem_setOf_eq,
    RobinCaps.ThinDomain.affP_fst, RobinCaps.ThinDomain.affP_snd, one_smul, harg p]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨by linarith, by linarith, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨by linarith, by linarith, h3⟩

theorem zero_mem_bodyShift_cg (C : Cap m) : (0 : CapSpace m) ∈ bodyShift_cg C := by
  rw [bodyShift_eq_cg]
  have hK := C.hK
  have h1 : (0 : CapSpace m).1 = (0 : ℝ) := rfl
  have h2 : (0 : CapSpace m).2 = (0 : EuclideanSpace ℝ (Fin m)) := rfl
  have heq : (0 : ℝ) - C.K / 2 = -C.K / 2 := by ring
  refine ⟨by rw [h1]; linarith, by rw [h1]; linarith, ?_⟩
  rw [h1, h2, norm_zero, heq]
  exact C.θ_pos (-C.K / 2) ⟨by linarith, by linarith⟩

theorem isOpen_bodyShift_cg (C : Cap m) : IsOpen (bodyShift_cg C) :=
  (isOpen_body_cg C).preimage (RobinCaps.ThinDomain.continuous_affP (-C.K / 2) 1 1)

theorem convex_bodyShift_cg (C : Cap m) : Convex ℝ (bodyShift_cg C) := by
  rw [bodyShift_eq_cg]
  have hconc : ConcaveOn ℝ (Set.Ioo (-C.K / 2) (C.K / 2)) (fun x : ℝ => C.θ (x - C.K / 2)) :=
    RobinCaps.Domain.concaveOn_comp_affine (c := (1 : ℝ)) (d := -C.K / 2) C.θ_concave
      (convex_Ioo _ _) (fun x => by ring)
      (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  have hconv := RobinCaps.Domain.convex_of_concave_radius (m := m)
    (convex_Ioo (-C.K / 2) (C.K / 2)) hconc
  have heq : {p : CapSpace m | p.1 ∈ Set.Ioo (-C.K / 2) (C.K / 2) ∧ ‖p.2‖ < C.θ (p.1 - C.K / 2)}
      = {p : CapSpace m | -C.K / 2 < p.1 ∧ p.1 < C.K / 2 ∧ ‖p.2‖ < C.θ (p.1 - C.K / 2)} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_Ioo]
    tauto
  rwa [heq] at hconv

theorem isBounded_bodyShift_cg (C : Cap m) : Bornology.IsBounded (bodyShift_cg C) := by
  have hsub : bodyShift_cg C ⊆
      Set.Ioo (-C.K / 2) (C.K / 2) ×ˢ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1 := by
    rw [bodyShift_eq_cg]
    rintro p ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2⟩, ?_⟩
    have hI : p.1 - C.K / 2 ∈ Set.Ioo (-C.K) 0 := ⟨by linarith, by linarith⟩
    have hle : C.θ (p.1 - C.K / 2) ≤ 1 := C.θ_le_one _ hI
    simp only [Metric.mem_ball, dist_eq_norm, sub_zero]
    exact h3.trans_le hle
  exact (Bornology.IsBounded.prod (Metric.isBounded_Ioo _ _) Metric.isBounded_ball).subset hsub

theorem measurableSet_bodyShift_cg (C : Cap m) : MeasurableSet (bodyShift_cg C) :=
  (RobinCaps.ThinDomain.measurableSet_capBody C).preimage
    (RobinCaps.ThinDomain.measurable_affP (-C.K / 2) 1 1)

end RobinCaps.Cap
