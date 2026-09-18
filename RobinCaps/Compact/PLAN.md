# `RobinCaps/Compact/` — Rellich–Kondrachov on the ball and the transverse ground state

Design note for the compactness sub-project (Lean 4.26 / Mathlib v4.26.0).  All files live under
`RobinCaps/Compact/`; nothing outside this directory is edited.  Ambient conventions:

* `E := EuclideanSpace ℝ (Fin n)`, `B_R := Metric.ball (0 : E) R`, Lebesgue measure `volume`.
* `Weak.H1 D` (file `RobinCaps/Sobolev/Weak.lean`): `toFun`, `grad`, `memL2`, `grad_memL2`,
  `hasWeakGrad`; forms `Weak.mass u = ∫_D u²`, `Weak.dirichlet u = ∫_D ‖∇u‖²`.
* Convolutions are scalar, with respect to Lebesgue measure: `ρ ⋆[lsmul ℝ ℝ, volume] g`,
  i.e. `x ↦ ∫ t, ρ t * g (x - t)` (`IsMollifier.conv_apply`).
* `IsMollifier δ ρ` (file `Basic.lean`): `ρ` smooth, `≥ 0`, `∫ ρ = 1`, `tsupport ρ ⊆ closedBall 0 δ`.
  Concrete instance: `mollifier δ = (bump δ).normed volume`, `isMollifier_mollifier (hδ : 0 < δ)`.
* Zero extensions (file `Basic.lean`): for `u : H1 B_R`, `ext u := B_R.indicator u.toFun`,
  `extGrad u i := B_R.indicator (fun y => u.grad y i)`; both are in `L²(E)`, integrable, compactly
  supported; `∫ (ext u)² = mass u`, `∑ᵢ ∫ (extGrad u i)² = dirichlet u`.
* `L2B n R := Lp ℝ 2 (volume.restrict B_R)`, `toL2 u := u.memL2.toLp u.toFun`,
  `dist (hf.toLp f) (hg.toLp g) ^ 2 = ∫ x in B_R, (f x - g x) ^ 2`.

## 0. Mathematical route (why this and not the textbook one)

The textbook proof extends `u ∈ H¹(B)` to `H¹(ℝⁿ)` by reflection or by the Lipschitz extension
theorem; neither is in mathlib.  Instead we use that the ball is **star-shaped**:

1. **Dilation.**  `D_λ u (x) := u (λ x)` for `1/2 ≤ λ < 1` lives in `H¹(B_{R/λ})`, a ball strictly
   larger than `B_R`, and `‖D_λ u - u‖_{L²(B_R)} ≤ 2^{n/2} (1-λ) R ‖∇u‖_{L²(B_R)}`.
2. **Mollification.**  For `ε < R/λ - R`, `S_ε(D_λ u) := ρ_ε ⋆ ext(D_λ u)` is smooth on all of `ℝⁿ`,
   and `‖S_ε w - w‖_{L²(B_R)} ≤ ε ‖∇w‖_{L²(B_{R/λ})}` for `w = D_λ u`.
3. **Arzelà–Ascoli.**  `S_ε(D_λ u_k)` is uniformly bounded and uniformly Lipschitz (bounds through
   `‖ρ_ε‖_{L²}`, `‖∇ρ_ε‖_{L²}` and `‖u_k‖_{L²}` only), hence totally bounded in `L²(B_R)`.
4. **Total boundedness.**  A sequence that is uniformly `η`-close to a totally bounded sequence for
   every `η > 0` has totally bounded range; `L²` is complete, so it has a convergent subsequence.

Every *weak* fact is used through a single identity (WG): for `x` with `‖x‖ + δ < R`,
`∂ᵢ (ρ_δ ⋆ ext u)(x) = (ρ_δ ⋆ extGrad u i)(x)` — the weak-gradient definition applied to the
test function `y ↦ ρ_δ (x - y)`.  Everything else concerns smooth functions (classical calculus),
or `L²` functions (Jensen/Tonelli, density of `C_c`).

For the ground state (Part 2) the boundary form is **not** obtained from a trace operator.  For
`C¹` functions on the closed ball the divergence theorem (proved here by the radial fundamental
theorem of calculus and polar coordinates) gives the *Rellich identity*

`∫_{∂B_R} u v dσ = R⁻¹ ∫_{B_R} ( m u v + u ⟪x, ∇v⟫ + v ⟪x, ∇u⟫ ) dx`,

whose right-hand side makes sense for `u, v ∈ H¹(B_R)` and is continuous in `H¹`.  We *define*
`bdR u v` by the right-hand side.  It is bilinear, symmetric, vanishes on a.e.-null elements,
bounded by the `H¹` norm, equals the true sphere integral on `C¹` functions and (by density,
Part 1) is nonnegative.  Its value on constants is `|∂B_R| = m ω_m R^{m-1}`.  This is the unique
`H¹`-continuous extension of the boundary integral, i.e. the form `∫ (Tr u)(Tr v)` of the
manuscript, without constructing `Tr`.

The gap `λ₂ − ν_R ≥ c R⁻²` (field `TransverseGroundState.gap`) is obtained **for small `R`**,
exactly as in the manuscript (lines 485–489), from: the Poincaré–Wirtinger inequality on the
ball (itself a corollary of Rellich), the trial bound `ν_R ≤ m α / R` (test function `1`), and the
resulting closeness of `ψ_R` to a constant.  No simplicity of `λ₁` and no sphere-Laplacian
spectral gap is needed for the *existence* of a positive gap constant; the explicit constant
`λ₁(S^{m-1}) = m-1` (Part 3 of the brief) would only sharpen `c`.

## 1. File DAG

```
Basic.lean                                   (shared definitions; done)
 ├─ Contraction.lean      (J)   ∫ |ρ ⋆ g|² ≤ ∫ |g|²  for a probability kernel
 ├─ SmoothEstimates.lean  (S-smooth), (D-smooth) for global C¹ functions
 ├─ WeakGradMollify.lean  (WG) ∂ᵢ(ρ ⋆ ext u) = ρ ⋆ extGrad u i on the interior
 ├─ Dilation.lean         D_λ : H1 B_R → H1 B_{R/λ}; scaling of mass, dirichlet
 ├─ TotallyBounded.lean   abstract metric-space lemmas
 ├─ ArzelaAscoli.lean     bounded + Lipschitz sequence ⇒ totally bounded in L2B
 ├─ H1Limit.lean          H¹-Cauchy sequences have a limit in H1 (weak gradient closed)
 └─ BoundaryForm.lean     bdR, algebra, bound, value on constants, Rellich identity for C¹
      │
 L2Approx.lean   (M) ρ_δ ⋆ g → g in L²(E); (M') g(λ·) → g in L²(E)      [needs Contraction]
      │
 Approx.lean     ‖S_ε D_λ u − u‖_{L²(B_R)} bound; ∇(S_ε D_λ u) → ∇u in L²(B_R)
      │                                     [needs Contraction, SmoothEstimates, WeakGradMollify, Dilation, L2Approx]
 Rellich.lean    rellich_ball : Weak.RellichEmbedding (ball 0 R)     [needs all of the above]
      │
 Poincare.lean   zero weak gradient ⇒ a.e. constant; Poincaré–Wirtinger on B_R with C·R²
 BoundaryNonneg.lean  0 ≤ bdR u u (density)                          [needs Approx, BoundaryForm]
 Minimiser.lean  existence of the Rayleigh minimiser; first variation
 GroundStateExists.lean  HasTransverseGroundState m α R (bdR m R) for 0 < R < R₀
```

## 2. Exact statements

Notation below: `⋆` means `⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]`; `hρ : IsMollifier δ ρ`.

### Contraction.lean  (namespace `RobinCaps.Compact`)

```lean
theorem lintegral_conv_sq_le (hρ : IsMollifier δ ρ) {g : E → ℝ} (hg : AEStronglyMeasurable g volume) :
    ∫⁻ x, ENNReal.ofReal ((ρ ⋆ g) x ^ 2) ≤ ∫⁻ x, ENNReal.ofReal (g x ^ 2)
theorem memLp_conv (hρ : IsMollifier δ ρ) {g : E → ℝ} (hg : MemLp g 2 volume) : MemLp (ρ ⋆ g) 2 volume
theorem integral_conv_sq_le (hρ : IsMollifier δ ρ) {g : E → ℝ} (hg : MemLp g 2 volume) :
    ∫ x, (ρ ⋆ g) x ^ 2 ≤ ∫ x, g x ^ 2
theorem integral_conv_sub_sq_le (hρ : IsMollifier δ ρ) {g h : E → ℝ} (hg : MemLp g 2 volume) (hh : MemLp h 2 volume) :
    ∫ x, ((ρ ⋆ g) x - (ρ ⋆ h) x) ^ 2 ≤ ∫ x, (g x - h x) ^ 2
/-- Pointwise Cauchy–Schwarz bounds. -/
theorem abs_conv_le (hρ) {g} (hg : MemLp g 2 volume) (x : E) :
    |(ρ ⋆ g) x| ≤ Real.sqrt (∫ t, ρ t ^ 2) * Real.sqrt (∫ t, g t ^ 2)
```
Proof of the first: pointwise `ofReal ((∫ ρ(t) g(x−t))²) ≤ ∫⁻ ofReal(ρ t) · ofReal(g(x−t)²)` (Cauchy–Schwarz /
`ENNReal.lintegral_mul_le_Lp_mul_Lq` with `ρ = √ρ·√ρ`, using `∫⁻ ofReal ρ = 1`), then Tonelli
(`lintegral_lintegral_swap`) and translation invariance (`lintegral_sub_right_eq_self`).

### SmoothEstimates.lean

```lean
/-- (S-smooth) -/
theorem integral_ball_conv_sub_sq_le (hρ : IsMollifier ε ρ) (hε : 0 ≤ ε) {v : E → ℝ} (hv : ContDiff ℝ 1 v)
    {r : ℝ} (hr : 0 ≤ r) :
    ∫ x in ball (0:E) r, ((ρ ⋆ v) x - v x) ^ 2 ≤ ε ^ 2 * ∫ x in ball (0:E) (r + ε), ‖fderiv ℝ v x‖ ^ 2
/-- (D-smooth) -/
theorem integral_ball_dilate_sub_sq_le {v : E → ℝ} (hv : ContDiff ℝ 1 v) {r : ℝ} (hr : 0 ≤ r)
    {lam : ℝ} (hlam : 1 / 2 ≤ lam) (hlam1 : lam ≤ 1) :
    ∫ x in ball (0:E) r, (v (lam • x) - v x) ^ 2
      ≤ (1 - lam) ^ 2 * r ^ 2 * 2 ^ n * ∫ x in ball (0:E) r, ‖fderiv ℝ v x‖ ^ 2
```
(S): `(ρ⋆v)(x) − v(x) = ∫ ρ(t)(v(x−t) − v(x)) dt`, `v(x−t) − v(x) = −∫₀¹ fderiv v (x − s t) t ds`,
Cauchy–Schwarz twice, Tonelli, `∫_{B_r} F(x − st) dx ≤ ∫_{B_{r+ε}} F` for `‖t‖ ≤ ε`.
(D): `v(x) − v(λx) = ∫_λ^1 fderiv v (s x) x ds`, `‖x‖ ≤ r`, Cauchy–Schwarz,
`∫_{B_r} F(s x) dx = s^{-n} ∫_{B_{sr}} F ≤ 2^n ∫_{B_r} F` (`Measure.integral_comp_smul`).

### WeakGradMollify.lean

```lean
/-- (WG) -/
theorem fderiv_conv_ext (hρ : IsMollifier δ ρ) (u : H1 (ball (0:E) R)) {x : E} (hx : ‖x‖ + δ < R) (i : Fin n) :
    fderiv ℝ (ρ ⋆ ext u) x (EuclideanSpace.single i 1) = (ρ ⋆ extGrad u i) x
theorem classicalGrad_conv_ext (hρ) (u) {x} (hx : ‖x‖ + δ < R) :
    Weak.classicalGrad (ρ ⋆ ext u) x = WithLp.toLp 2 (fun i => (ρ ⋆ extGrad u i) x)
theorem norm_fderiv_conv_ext_sq_le (hρ) (u) {x} (hx : ‖x‖ + δ < R) :
    ‖fderiv ℝ (ρ ⋆ ext u) x‖ ^ 2 ≤ ∑ i, ((ρ ⋆ extGrad u i) x) ^ 2
```
Proof: `HasCompactSupport.hasFDerivAt_convolution_left` gives `∂ᵢ(ρ ⋆ ext u)(x) = ∫ ∂ᵢρ(t) ext u (x−t) dt
= ∫ ∂ᵢρ(x − y) u(y) dy` (substitution `y = x − t`, `integral_sub_left_eq_self`), and with the test
function `φ(y) := ρ(x − y)` (smooth, `tsupport φ ⊆ closedBall x δ ⊆ B_R`, `∂ᵢφ(y) = −∂ᵢρ(x−y)`)
the definition `u.hasWeakGrad` gives `∫_B u ∂ᵢφ = −∫_B gᵢ φ`, i.e. the claim.

### Dilation.lean

```lean
def dilate {R : ℝ} (lam : ℝ) (hlam : 0 < lam) (u : H1 (ball (0:E) R)) : H1 (ball (0:E) (R / lam))
  -- toFun x = u.toFun (lam • x), grad x = lam • u.grad (lam • x)
theorem dilate_toFun, dilate_grad (simp)
theorem mass_dilate : mass (dilate lam hlam u) = lam⁻¹ ^ n * mass u
theorem dirichlet_dilate : dirichlet (dilate lam hlam u) = lam ^ 2 * lam⁻¹ ^ n * dirichlet u
theorem ext_dilate (hlam) (u) (x) : ext (dilate lam hlam u) x = ext u (lam • x)
theorem extGrad_dilate (hlam) (u) (i) (x) : extGrad (dilate lam hlam u) i x = lam * extGrad u i (lam • x)
/-- Transport along an equality of radii. -/
def castRadius {R R' : ℝ} (h : R = R') (u : H1 (ball (0:E) R)) : H1 (ball (0:E) R')
theorem castRadius_toFun, castRadius_grad, mass_castRadius, dirichlet_castRadius
/-- L² scaling for general functions. -/
theorem integral_ball_comp_smul_sq (g : E → ℝ) {lam : ℝ} (hlam : 0 < lam) (r : ℝ) :
    ∫ x in ball (0:E) r, g (lam • x) ^ 2 = lam⁻¹ ^ n * ∫ x in ball (0:E) (lam * r), g x ^ 2
```
Weak gradient of the dilation: for a test function `φ` on `B_{R/λ}`, `ψ(y) := φ(λ⁻¹ y)` is a test
function on `B_R` with `∂ᵢψ(y) = λ⁻¹ ∂ᵢφ(λ⁻¹ y)`; change variables with `Measure.integral_comp_smul`.

### TotallyBounded.lean

```lean
theorem totallyBounded_range_of_approx {X : Type*} [PseudoMetricSpace X] (w : ℕ → X)
    (h : ∀ η : ℝ, 0 < η → ∃ f : ℕ → X, TotallyBounded (Set.range f) ∧ ∀ k, dist (w k) (f k) ≤ η) :
    TotallyBounded (Set.range w)
theorem exists_subseq_tendsto_of_totallyBounded {X : Type*} [MetricSpace X] [CompleteSpace X]
    (w : ℕ → X) (h : TotallyBounded (Set.range w)) :
    ∃ (ν : ℕ → ℕ) (a : X), StrictMono ν ∧ Tendsto (w ∘ ν) atTop (𝓝 a)
```

### ArzelaAscoli.lean

```lean
theorem totallyBounded_range_toLp_of_lipschitz {R A : ℝ} {L : NNReal} (f : ℕ → E → ℝ)
    (hb : ∀ k x, |f k x| ≤ A) (hL : ∀ k, LipschitzWith L (f k))
    (hm : ∀ k, MemLp (f k) 2 (volume.restrict (ball (0:E) R))) :
    TotallyBounded (Set.range fun k => (hm k).toLp (f k))
```
Via `BoundedContinuousFunction.arzela_ascoli₂` on the compact `closedBall (0:E) R` (restrictions of
`f k` are in the closed, equicontinuous, bounded set `{F | ∀ x, |F x| ≤ A ∧ LipschitzWith L F}`),
`totallyBounded_iff_subset`, and `‖toLp f − toLp g‖ ≤ (vol B_R)^{1/2} · sup_{closedBall} |f − g|`
(`eLpNorm_le_of_ae_bound`).  Also provide the uniform bounds for mollified functions:
```lean
theorem abs_conv_le_of_memLp (hρ) {g} (hg : MemLp g 2 volume) (x) : |(ρ ⋆ g) x| ≤ √(∫ ρ²) * √(∫ g²)   -- from Contraction, or reprove
theorem lipschitzWith_conv (hρ) {g} (hg : MemLp g 2 volume) :
    LipschitzWith ⟨√(∫ t, ‖fderiv ℝ ρ t‖ ^ 2) * √(∫ t, g t ^ 2), _⟩ (ρ ⋆ g)
```
(`HasCompactSupport.hasFDerivAt_convolution_left`, `lipschitzWith_of_nnnorm_fderiv_le`).

### H1Limit.lean

```lean
theorem hasWeakGrad_of_tendsto {D : Set E} (u : ℕ → E → ℝ) (g : ℕ → E → E) (v : E → ℝ) (h : E → E)
    (hu : ∀ k, MemLp (u k) 2 (volume.restrict D)) ... (hv : MemLp v 2 ...) (hh : MemLp h 2 ...)
    (hw : ∀ k, HasWeakGrad D (u k) (g k))
    (hlim : Tendsto (fun k => ∫ x in D, (u k x - v x) ^ 2) atTop (𝓝 0))
    (hlimg : Tendsto (fun k => ∫ x in D, ‖g k x - h x‖ ^ 2) atTop (𝓝 0)) : HasWeakGrad D v h
/-- An H¹-Cauchy sequence has an H¹-limit in `H1 D`. -/
theorem exists_H1_limit {D : Set E} (hD : MeasurableSet D) (u : ℕ → H1 D)
    (hc : ∀ η > 0, ∃ N, ∀ k l, N ≤ k → N ≤ l → mass (u k - u l) + dirichlet (u k - u l) ≤ η) :
    ∃ v : H1 D, Tendsto (fun k => mass (u k - v) + dirichlet (u k - v)) atTop (𝓝 0)
```
(Completeness of `Lp` for `toFun` and for the vector-valued `grad`, then the first lemma.)

### BoundaryForm.lean  (uses `RobinCaps/ThinDomain/Polar.lean`)

```lean
def bdR (m : ℕ) (R : ℝ) : H1 (ball (0:E) R) →ₗ[ℝ] H1 (ball (0:E) R) →ₗ[ℝ] ℝ
  -- bdR m R u v = R⁻¹ * ∫ x in ball 0 R, (m * u x * v x + u x * ⟪x, v.grad x⟫ + v x * ⟪x, u.grad x⟫)
theorem bdR_apply, bdR_symm, bdR_vanishesOnNullAE : VanishesOnNullAE (ball 0 R) (bdR m R)
theorem bdR_bound (hR : 0 < R) (u) : |bdR m R u u| ≤ (m / R + 1) * mass u + dirichlet u
theorem bdR_bound₂ (hR) (u v) : |bdR m R u v| ≤ (m / R + 1) * √(mass u + dirichlet u) * √(mass v + dirichlet v)
/-- C¹ functions as elements of `H1 (ball 0 R)`. -/
def ofC1 (R : ℝ) (v : E → ℝ) (hv : ContDiff ℝ 1 v) : H1 (ball (0:E) R)   -- grad = classicalGrad v
/-- The Rellich / divergence identity for C¹ functions (radial FTC + polar coordinates). -/
theorem bdR_ofC1 (hm : 1 ≤ m) (hR : 0 < R) (v w : E → ℝ) (hv : ContDiff ℝ 1 v) (hw : ContDiff ℝ 1 w) :
    bdR m R (ofC1 R v hv) (ofC1 R w hw) = ThinDomain.sphereIntegral m R (fun z => v z * w z)
theorem bdR_const (hm : 1 ≤ m) (hR : 0 < R) : bdR m R (ofC1 R 1 _) (ofC1 R 1 _) = m * ThinDomain.omega m * R ^ (m - 1)
```

### L2Approx.lean  (needs Contraction)

```lean
/-- (M) -/
theorem exists_delta_conv_close {g : E → ℝ} (hg : MemLp g 2 volume) {η : ℝ} (hη : 0 < η) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∫ x, ((mollifier δ ⋆ g) x - g x) ^ 2 ≤ η
/-- (M') -/
theorem exists_lam_dilate_close {g : E → ℝ} (hg : MemLp g 2 volume) {η : ℝ} (hη : 0 < η) :
    ∃ lam₀ : ℝ, lam₀ < 1 ∧ ∀ lam : ℝ, lam₀ < lam → lam ≤ 1 → ∫ x, (g (lam • x) - g x) ^ 2 ≤ η
```
Via `MemLp.exists_hasCompactSupport_eLpNorm_sub_le` (approximate by continuous compactly supported
`g_c`), the contraction (J) resp. the scaling identity for the difference `g − g_c`, and
dominated convergence for `g_c` (`ContDiffBump.convolution_tendsto_right_of_continuous`, uniform
continuity on compacts).

### Approx.lean

```lean
def approx (u : H1 (ball (0:E) R)) (lam ε : ℝ) (hlam : 0 < lam) : E → ℝ := mollifier ε ⋆ ext (dilate lam hlam u)
/-- (A1) -/
theorem integral_ball_approx_sub_sq_le (hR : 0 < R) (u) {lam ε} (hlam : 1/2 ≤ lam) (hlam1 : lam < 1) (hε : 0 < ε) (hε' : R + ε < R / lam) :
    ∫ x in ball (0:E) R, (approx u lam ε _ x - u.toFun x) ^ 2 ≤ 2 ^ (n + 1) * (ε + (1 - lam) * R) ^ 2 * dirichlet u
/-- (A2) gradient convergence -/
theorem exists_approx_grad_close (hR : 0 < R) (u) {η} (hη : 0 < η) :
    ∃ lam₀ < 1, ∀ lam, lam₀ < lam → lam < 1 → ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
      ∫ x in ball (0:E) R, ‖Weak.classicalGrad (approx u lam ε _) x - u.grad x‖ ^ 2 ≤ η
```
Ingredients: (S-weak) `∫_{B_R} (S_ε w̄ − w̄)² ≤ ε² dirichlet w` for `w = dilate λ u` (apply (S-smooth) to
`v = S_δ w̄`, (WG) + (J) for the right-hand side, then `δ → 0` by (M) and (J)); (D-weak)
`∫_{B_R} (ū(λ·) − ū)² ≤ (1−λ)² R² 2ⁿ dirichlet u` (apply (D-smooth) on `B_r`, `r < R`, to `S_δ ū`, let
`δ → 0` by (M), then `r ↑ R` by monotone convergence).

### Rellich.lean

```lean
theorem rellich_ball (n : ℕ) {R : ℝ} (hR : 0 < R) :
    Weak.RellichEmbedding (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)
theorem rellich_ball' (hR : 0 < R) (u : ℕ → H1 (ball (0:E) R)) {M : ℝ} (hM : ∀ k, dirichlet (u k) + mass (u k) ≤ M) :
    ∃ (ν : ℕ → ℕ) (a : L2B n R), StrictMono ν ∧ Tendsto (fun k => toL2 (u (ν k))) atTop (𝓝 a)
```

### Part 2

```lean
-- Poincare.lean
theorem ae_const_of_grad_ae_zero (hR : 0 < R) (u : H1 (ball (0:E) R)) (h : u.grad =ᵐ[volume.restrict (ball 0 R)] 0) :
    ∃ c : ℝ, u.toFun =ᵐ[volume.restrict (ball (0:E) R)] fun _ => c
theorem poincare_wirtinger_unit (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ u : H1 (ball (0:E) 1),
    (∫ x in ball (0:E) 1, u.toFun x) = 0 → mass u ≤ C * dirichlet u
theorem poincare_wirtinger (hR : 0 < R) (u) (hmean : ∫ x in ball 0 R, u.toFun x = 0) : mass u ≤ C_P n * R ^ 2 * dirichlet u
-- BoundaryNonneg.lean
theorem bdR_nonneg (hm : 1 ≤ m) (hR : 0 < R) (u) : 0 ≤ bdR m R u u
-- Minimiser.lean  (for a general bd with: symmetric, nonneg, bounded by C·(mass+dirichlet), α ≥ 0)
def lam1 (α) (bd) : ℝ := sInf {t | ∃ u : H1 (ball 0 R), mass u = 1 ∧ t = dirichlet u + α * bd u u}
theorem exists_minimiser ... : ∃ ψ, mass ψ = 1 ∧ dirichlet ψ + α * bd ψ ψ = lam1 α bd ∧ ∀ v, lam1 α bd * mass v ≤ dirichlet v + α * bd v v
theorem weak_eq_of_minimiser ... : ∀ v, dirichletBilin ψ v + α * bd ψ v = lam1 α bd * massBilin ψ v
-- GroundStateExists.lean
theorem hasTransverseGroundState (m : ℕ) (hm : 1 ≤ m) {α : ℝ} (hα : 0 ≤ α) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, 0 < R → R < R₀ → ThinDomain.HasTransverseGroundState m α R (bdR m R)
```
Minimiser: for a minimising sequence normalised by `mass = 1`, the parallelogram identity for the
form `q + N` and `q ≥ λ₁ N` give `(q+N)[(u_k − u_l)/2] ≤ (q+N)[u_k]/2 + (q+N)[u_l]/2 − (λ₁+1)(1 − N[(u_k−u_l)/2])`,
so along the Rellich subsequence (`L²`-Cauchy) the sequence is `H¹`-Cauchy; `H1Limit` gives the
limit `ψ`, continuity of `q` (bound on `bd`) gives `q[ψ] = λ₁`; the first variation of
`t ↦ q[ψ + t v] − λ₁ N[ψ + t v] ≥ 0` gives the weak eigenvalue equation.
Gap: for `v ⊥ ψ`, `q[v] − ν N[v] ≥ dirichlet[v] − ν N[v] ≥ μ₂(R)(N[v] − |B| v̄²) − ν N[v]` with
`μ₂(R) = 1/(C_P R²)`, `ν ≤ mα/R` (test function `1`, `bdR_const`, `volume_ball`), and
`|B| v̄² ≤ θ(R) N[v]` with `θ(R) = C_P m α R / (1 − C_P m α R)` (since `(∫ v)² = ⟪v, 1 − ψ/ψ̄⟫² ≤ N[v] ‖ψ − ψ̄‖²/ψ̄²`
and `‖ψ − ψ̄‖² ≤ C_P R² dirichlet ψ ≤ C_P m α R`).  For `R` small this is `≥ (1/(2 C_P)) R⁻² N[v]`.

## 3. Status

Complete for items 1 and 2 of the brief: see `STATUS.md` for the file table, the `#print axioms`
output of the main theorems, the caveats (small `R` only; weak rather than `C¹` ground state;
`bdR` instead of a trace) and the wiring instructions.  Item 3 (sphere-Laplacian gap) was not
attempted (see `STATUS.md`).  Two actual file names differ from the DAG above: the ground-state
construction with hypotheses is `GroundStateGap.lean`, and `GroundStateExists.lean` discharges them.
