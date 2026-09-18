import RobinCaps.Compact.Approx
import RobinCaps.Compact.BoundaryForm
import RobinCaps.Compact.Minimiser
import RobinCaps.Compact.H1Limit

/-!
# Nonnegativity of the Rellich boundary form

The boundary form `bdR n R` of `RobinCaps/Compact/BoundaryForm.lean` is defined by the
right-hand side of the Rellich identity, so its nonnegativity on the diagonal is not visible from
the definition.  It follows by density:

* `exists_ofC1_h1_close` — every `u ∈ H¹(B_R)` is the `H¹`-limit of `C¹` functions
  (`ofC1 R v hv`).  The approximants are the smooth `approx u lam ε` of
  `RobinCaps/Compact/Approx.lean`: the `L²` error is controlled by
  `integral_ball_approx_sub_sq_le'`, the gradient error by `exists_approx_grad_close`; the two
  parameters `lam` (dilation) and `ε` (mollification) are chosen so that both are small.
* `bdR_nonneg` — `0 ≤ bdR n R u u`.  On `C¹` functions `bdR` is the sphere integral of `v²`
  (`bdR_ofC1`), hence nonnegative; the diagonal of the bounded symmetric form `bdR` is continuous
  in `H¹` (`abs_bilin_self_sub_le` of `RobinCaps/Compact/Minimiser.lean` with the bound
  `abs_bdR_le₂`), so the inequality passes to the limit.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

open MeasureTheory Metric Set Filter

open scoped Convolution ContDiff ENNReal Topology

namespace RobinCaps.Compact

open RobinCaps.Sobolev.Weak

variable {n : ℕ}

/-- The ambient Euclidean space `ℝⁿ`. -/
local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ## Density of `C¹` functions in `H¹(B_R)` -/

/-- **Density of `C¹` functions in `H¹(B_R)`**: for every `u ∈ H¹(B_R)` and `η > 0` there is a
`C¹` function `v` on `E` with `‖ofC1 R v - u‖²_{H¹(B_R)} ≤ η`. -/
theorem exists_ofC1_h1_close {R : ℝ} (hR : 0 < R) (u : H1 (ball (0 : E) R)) {η : ℝ}
    (hη : 0 < η) :
    ∃ (v : E → ℝ) (hv : ContDiff ℝ 1 v),
      mass (ofC1 R v hv - u) + dirichlet (ofC1 R v hv - u) ≤ η := by
  have hη2 : 0 < η / 2 := by positivity
  have hD : 0 ≤ dirichlet u := dirichlet_nonneg u
  -- the threshold `lam₀` for the gradient error
  obtain ⟨lam₀, hlam₀, hlam₀1, hgrad⟩ := exists_approx_grad_close hR u hη2
  -- the length scale `t` controlling the `L²` error
  set A : ℝ := 8 * 2 ^ n * (dirichlet u + 1) with hA
  have hApos : 0 < A := by positivity
  set t : ℝ := min 1 (min (R / 2) (η / A)) with ht
  have ht0 : 0 < t := by
    simp only [ht, lt_min_iff]
    exact ⟨one_pos, by positivity, by positivity⟩
  have ht1 : t ≤ 1 := min_le_left _ _
  have htR : t ≤ R / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have htA : t ≤ η / A := (min_le_right _ _).trans (min_le_right _ _)
  have htA' : t * A ≤ η := by
    rw [le_div_iff₀ hApos] at htA
    exact htA
  have hmassbound : 2 ^ n * (2 * t) ^ 2 * dirichlet u ≤ η / 2 := by
    have h2n : (0 : ℝ) < 2 ^ n := by positivity
    have hsq : (2 * t) ^ 2 ≤ 4 * t := by nlinarith
    calc 2 ^ n * (2 * t) ^ 2 * dirichlet u
        ≤ 2 ^ n * (4 * t) * dirichlet u := by gcongr
      _ ≤ 2 ^ n * (4 * t) * (dirichlet u + 1) := by gcongr; linarith
      _ = t * A / 2 := by rw [hA]; ring
      _ ≤ η / 2 := by linarith
  -- the dilation parameter
  set lam : ℝ := max ((lam₀ + 1) / 2) (1 - t / R) with hlam
  have hlam₀lt : lam₀ < lam := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hlam1 : lam < 1 := max_lt (by linarith) (by
    have : 0 < t / R := by positivity
    linarith)
  have hlam12 : 1 / 2 ≤ lam := le_trans (by linarith) (le_max_left _ _)
  have hlam0 : 0 < lam := by linarith
  have hlamt : (1 - lam) * R ≤ t := by
    have h1 : 1 - t / R ≤ lam := le_max_right _ _
    have h2 : (1 - lam) ≤ t / R := by linarith
    calc (1 - lam) * R ≤ t / R * R := by gcongr
      _ = t := by field_simp
  -- the mollification parameter
  obtain ⟨ε₀, hε₀, hε⟩ := hgrad lam hlam₀lt hlam1 hlam0
  set ε : ℝ := min (ε₀ / 2) t with hεdef
  have hε0 : 0 < ε := lt_min (by positivity) ht0
  have hεε₀ : ε < ε₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hεt : ε ≤ t := min_le_right _ _
  obtain ⟨hε', hgradε⟩ := hε ε hε0 hεε₀
  -- the approximant
  set v : E → ℝ := approx u lam ε hlam0 with hv
  have hvC1 : ContDiff ℝ 1 v := (contDiff_approx u hlam0 hε0).of_le (by simp)
  refine ⟨v, hvC1, ?_⟩
  -- the `L²` error
  have hmass : mass (ofC1 R v hvC1 - u) ≤ η / 2 := by
    rw [mass_sub, ofC1_toFun]
    have h1 := integral_ball_approx_sub_sq_le' hR u hlam12 hlam1 hε0 hε' hlam0
    have h2 : (ε + (1 - lam) * R) ^ 2 ≤ (2 * t) ^ 2 := by
      have h3 : 0 ≤ ε + (1 - lam) * R := by
        have : 0 ≤ (1 - lam) * R := mul_nonneg (by linarith) hR.le
        linarith
      have h4 : ε + (1 - lam) * R ≤ 2 * t := by linarith
      exact pow_le_pow_left₀ h3 h4 2
    calc ∫ x in ball (0 : E) R, (v x - u.toFun x) ^ 2
        ≤ 2 ^ n * (ε + (1 - lam) * R) ^ 2 * dirichlet u := h1
      _ ≤ 2 ^ n * (2 * t) ^ 2 * dirichlet u := by gcongr
      _ ≤ η / 2 := hmassbound
  -- the gradient error
  have hdir : dirichlet (ofC1 R v hvC1 - u) ≤ η / 2 := by
    rw [dirichlet_sub, ofC1_grad]
    exact hgradε
  linarith

/-! ## Nonnegativity of the boundary form -/

/-- On `C¹` functions the diagonal of the boundary form is a sphere integral of a square, hence
nonnegative. -/
theorem bdR_ofC1_self_nonneg (hn : 1 ≤ n) {R : ℝ} (hR : 0 < R) (v : E → ℝ)
    (hv : ContDiff ℝ 1 v) : 0 ≤ bdR n R (ofC1 R v hv) (ofC1 R v hv) := by
  rw [bdR_ofC1 hn hR v v hv hv]
  exact ThinDomain.sphereIntegral_nonneg n hR.le fun z => mul_self_nonneg (v z)

/-- **Nonnegativity of the Rellich boundary form** (by density of `C¹` functions). -/
theorem bdR_nonneg (hn : 1 ≤ n) {R : ℝ} (hR : 0 < R) (u : H1 (ball (0 : E) R)) :
    0 ≤ bdR n R u u := by
  -- the constants
  set C : ℝ := (n : ℝ) / R + 1 with hCdef
  have hC : 0 ≤ C := by positivity
  set K : ℝ := mass u + dirichlet u with hKdef
  have hK : 0 ≤ K := add_nonneg (mass_nonneg u) (dirichlet_nonneg u)
  set M : ℝ := C * (1 + 2 * Real.sqrt K) + 1 with hMdef
  have hM1 : 1 ≤ M := by
    have : 0 ≤ C * (1 + 2 * Real.sqrt K) := mul_nonneg hC (by positivity)
    linarith
  have hM : 0 < M := by linarith
  -- the continuity estimate for the diagonal
  have he : ∀ w : H1 (ball (0 : E) R), 0 ≤ mass w + dirichlet w :=
    fun w => add_nonneg (mass_nonneg w) (dirichlet_nonneg w)
  have hcont := abs_bilin_self_sub_le (F := bdR n R) (fun a b => bdR_symm a b)
    (e := fun w : H1 (ball (0 : E) R) => mass w + dirichlet w) he (C := C)
    (fun a b => abs_bdR_le₂ hR a b)
  -- it suffices to show `a ≤ bdR u u` for every `a < 0`
  refine le_of_forall_lt_imp_le_of_dense fun a ha => ?_
  set δ : ℝ := -a with hδdef
  have hδ : 0 < δ := by linarith
  -- the closeness level
  set η : ℝ := min 1 ((δ / M) ^ 2) with hηdef
  have hη : 0 < η := lt_min one_pos (by positivity)
  obtain ⟨v, hv, hclose⟩ := exists_ofC1_h1_close hR u hη
  set w : H1 (ball (0 : E) R) := ofC1 R v hv with hwdef
  set e : ℝ := mass (w - u) + dirichlet (w - u) with hedef
  have he0 : 0 ≤ e := he _
  have heη : e ≤ η := hclose
  have hw : 0 ≤ bdR n R w w := bdR_ofC1_self_nonneg hn hR v hv
  have hdiff := hcont w u
  simp only at hdiff
  -- `√e ≤ δ / M` and `e ≤ √e`
  set s : ℝ := Real.sqrt e with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg e
  have hss : s * s = e := Real.mul_self_sqrt he0
  have hs1 : s ≤ 1 := by
    rw [hsdef, Real.sqrt_le_one]
    exact heη.trans (min_le_left _ _)
  have hsδ : s ≤ δ / M := by
    rw [hsdef]
    calc Real.sqrt e ≤ Real.sqrt ((δ / M) ^ 2) :=
          Real.sqrt_le_sqrt (heη.trans (min_le_right _ _))
      _ = δ / M := Real.sqrt_sq (by positivity)
  have hes : e ≤ s := by nlinarith
  -- the error is at most `δ`
  have hbound : C * (e + 2 * s * Real.sqrt K) ≤ δ := by
    have hsqK : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
    have h1 : C * (e + 2 * s * Real.sqrt K) ≤ s * (C * (1 + 2 * Real.sqrt K)) := by
      have : C * (e + 2 * s * Real.sqrt K) ≤ C * (s + 2 * s * Real.sqrt K) := by
        gcongr
      linarith [this]
    have h2 : s * (C * (1 + 2 * Real.sqrt K)) ≤ δ / M * (M - 1) := by
      have hpos : 0 ≤ C * (1 + 2 * Real.sqrt K) := mul_nonneg hC (by positivity)
      calc s * (C * (1 + 2 * Real.sqrt K)) ≤ δ / M * (C * (1 + 2 * Real.sqrt K)) := by gcongr
        _ = δ / M * (M - 1) := by rw [hMdef]; ring
    have h3 : δ / M * (M - 1) ≤ δ := by
      have : δ / M * (M - 1) = δ - δ / M := by field_simp
      rw [this]
      have : 0 ≤ δ / M := by positivity
      linarith
    linarith
  -- conclude
  have habs := abs_le.mp hdiff
  rw [hδdef] at hbound
  linarith [habs.1, habs.2]

end RobinCaps.Compact
