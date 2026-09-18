# `RobinCaps/Compact/` — status

Updated as files land.  "compiles" means `lake env lean <file>` reports no errors and no
`sorry`; `#print axioms` for the main theorems is recorded at the end.

| File | Contents | Status |
|---|---|---|
| `Basic.lean` | `IsMollifier`, `mollifier δ`, `ext`, `extGrad`, `L2B`, `toL2`, `dist_toLp_sq` | compiles |
| `TotallyBounded.lean` | `totallyBounded_range_of_approx`, `exists_subseq_tendsto_of_totallyBounded` | compiles |
| `Contraction.lean` | (J) `lintegral_conv_sq_le`, `integral_conv_sq_le`, `integral_conv_sub_sq_le`, `memLp_conv`, `abs_conv_le` | compiles (203 lines) |
| `SmoothEstimates.lean` | (S-smooth) `integral_ball_conv_sub_sq_le`, (D-smooth) `integral_ball_dilate_sub_sq_le` | compiles (534 lines) |
| `WeakGradMollify.lean` | (WG) `fderiv_conv_ext`, `classicalGrad_conv_ext`, `norm_fderiv_conv_ext_eq`, `norm_fderiv_eq_norm_classicalGrad` | compiles (201 lines) |
| `Dilation.lean` | `dilate`, `castRadius`, `hasWeakGrad_comp_smul`, scaling identities | compiles (348 lines) |
| `ArzelaAscoli.lean` | `totallyBounded_range_toLp_of_lipschitz`, `abs_conv_le_sqrt`, `lipschitzWith_conv`, `memLp_ball_of_continuous` | compiles (297 lines) |
| `H1Limit.lean` | `hasWeakGrad_of_tendsto`, `exists_H1_limit`, `dist_toLp_sq_gen`, `tendsto_integral_mul`, `mass_sub`, `dirichlet_sub` | compiles (268 lines) |
| `BoundaryForm.lean` | `bdR`, `bdR_symm`, `bdR_vanishesOnNullAE`, `abs_bdR_le`, `abs_bdR_le₂`, `ofC1`, Rellich identity `bdR_ofC1`, `bdR_const` | compiles (625 lines) |
| `L2Approx.lean` | (M) `exists_delta_conv_close`, (M') `exists_lam_dilate_close`, Minkowski helper `sqrt_integral_sub_sq_le_add` | compiles (438 lines) |
| `Approx.lean` | (S-weak) `integral_ball_conv_ext_sub_sq_le`, (D-weak) `integral_ball_ext_dilate_sub_sq_le`, `approx`, (A1) `integral_ball_approx_sub_sq_le`, (A2) `exists_approx_grad_close` | compiles (718 lines) |
| `Rellich.lean` | **`rellich_ball : Weak.RellichEmbedding (ball 0 R)`**, `rellich_ball'`, `rellichSeq`, `rellichSeq'` | compiles (180 lines), axioms `[propext, Classical.choice, Quot.sound]` |
| `Poincare.lean` | `ae_const_of_grad_ae_zero`, `poincare_wirtinger_unit`, `poincare_wirtinger_ball` (Rellich as hypothesis `RellichSeq'`) | compiles (409 lines) |
| `BoundaryNonneg.lean` | `exists_ofC1_h1_close` (C¹ density in `H¹(B_R)`), `bdR_nonneg` | compiles (196 lines) |
| `RayleighAlgebra.lean` | `bilin_parallelogram`, `bilin_sub_le_of_lower`, `bilin_eq_of_isMin`, `bilin_cauchy_schwarz` | compiles |
| `Minimiser.lean` | `lam1`, `exists_minimiser`, `weak_eq_of_minimiser`, `exists_NB_eq_one`, `exists_minimiser'` (Rellich as hypothesis `RellichSeq`, boundary form as `GoodBd`) | compiles (423 lines) |
| `GroundStateGap.lean` | `goodBd_bdR`, `lam1_bdR_le`, `hasTransverseGroundState_of` (Rellich and `0 ≤ bdR` as hypotheses; `R₀ = min 1 (1/(8C(nα+1)))`, `gapConst = 1/(2C)`) | compiles (399 lines) |
| `GroundStateExists.lean` | **`hasTransverseGroundState_bdR (n) (hn : 1 ≤ n) (hα : 0 ≤ α) : ∃ R₀ > 0, ∀ R, 0 < R → R < R₀ → HasTransverseGroundState n α R (bdR n R)`** | compiles, axioms `[propext, Classical.choice, Quot.sound]` |

## Summary (2026-09-17)

All 20 files under `RobinCaps/Compact/` compile (`lake build RobinCaps.Compact.GroundStateExists`
builds the whole tree, 5772 lines); no `sorry`, `admit`, `axiom`, `native_decide` anywhere.

`#print axioms` (recorded at the end of `GroundStateExists.lean` and `Rellich.lean`):

```
'RobinCaps.Compact.hasTransverseGroundState_bdR' depends on axioms: [propext, Classical.choice, Quot.sound]
'RobinCaps.Compact.rellich_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'RobinCaps.Compact.bdR_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RobinCaps.Compact.bdR_ofC1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RobinCaps.Compact.poincare_wirtinger_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Delivered (brief items 1 and 2)

1. **Rellich–Kondrachov on the ball**: `rellich_ball (n) (hR : 0 < R) : Weak.RellichEmbedding (ball (0 : EuclideanSpace ℝ (Fin n)) R)`
   — exactly the target `Prop` of `RobinCaps/Sobolev/Weak.lean`; also the `Lp` form `rellich_ball'`.
2. **Transverse ground state**: `hasTransverseGroundState_bdR`, i.e. `HasTransverseGroundState n α R (bdR n R)`
   for `1 ≤ n`, `0 ≤ α`, `0 < R < R₀(n, α)`, where `bdR n R` is the Rellich-identity boundary form.
   Constants: `R₀ = min 1 (1 / (8 C (n α + 1)))`, `gapConst = 1 / (2 C)`, `C` the Poincaré–Wirtinger constant of the unit ball.
   Along the way: Poincaré–Wirtinger on `B_R` (`mass u ≤ C R² dirichlet u` for mean-zero `u`),
   density of `C¹` functions in `H¹(B_R)` (`exists_ofC1_h1_close`), the Rellich/divergence identity
   on the ball for `C¹` functions (`bdR_ofC1`, equality with `ThinDomain.sphereIntegral`), the trial
   bound `ν_R ≤ n α / R` (`lam1_bdR_le`), existence of the Rayleigh minimiser and its weak eigen-equation.

### Not delivered / caveats

* Brief item 3 (`λ₁(S^{m−1}) = m − 1`) was not attempted: mathlib has no Laplace–Beltrami operator on
  the sphere, and the positive gap constant of item 2 does not need it (only an explicit value of `c` would).
* The gap is proved for **small `R` only** (`R < R₀`), as in the manuscript (`TransverseGapTarget`).
  For large `R` the gap `λ₂ > λ₁` would need simplicity of the ground state (Harnack), which is out of reach.
* (Superseded 2026-09-18.) The `C¹` ground state required by `ThinDomain.TransverseGroundStateReg`
  (`Trial.lean`) is now provided by `GroundStateReg.lean` (radial power-series construction), see below.
* The boundary form is `bdR` (Rellich identity), not "`sphereIntegral` of a trace"; it agrees with the
  sphere integral on `C¹` functions and is the unique `H¹`-continuous extension, so it is the form
  `∫_{∂B_R} (Tr u)(Tr v) dσ` of the manuscript without constructing `Tr`.

### Wiring for the coordinator

Nothing outside `RobinCaps/Compact/` was edited.  Entry points to import:
`RobinCaps.Compact.Rellich` (`rellich_ball`), `RobinCaps.Compact.GroundStateExists`
(`hasTransverseGroundState_bdR`, `bdR`, `bdR_ofC1`, `bdR_const`).  The two `#print axioms`
commands at the end of `Rellich.lean` and `GroundStateExists.lean` print at build time; remove them
if the info output is unwanted.

## Regularity extension (2026-09-18, COMPLETE; see `PLAN_REG.md`)

| File | Contents | Status |
|---|---|---|
| `DivergenceBall.lean` | `integral_ball_div_radial` (divergence theorem for fields `h(z) z`) | compiles (haiku) |
| `PiconePointwise.lean` | pointwise Picone identity | compiles (haiku) |
| `RadialFun.lean` | `radialFun g z = g (‖z‖²)`, gradient, "Laplacian" | compiles (haiku) |
| `GradCalc.lean` | `classicalGrad` calculus (sum, product, quotient, chain, `‖z‖²`) | compiles (haiku + sonnet) |
| `RadialSeries.lean` | `radCoeff`, `radSeries`, `radSeries'`, `radSeries''`, summability, `hasDerivAt_radSeries`, `contDiff_radSeries`, `radSeries_ode` | compiles (sonnet, 541 lines; haiku attempt failed) |
| `RadialSeriesCont.lean` | `continuous_radSeries_pair`, `continuous_radSeries'_pair`, `radSeries_zero_nu`, `radSeries_ode'` | compiles (sonnet, 174 lines) |
| `RadialODEUnique.lean` | `radialODE_zero_of_zero_deriv_zero`, `radialODE_zero_at_zero` | compiles (sonnet, 145 lines) |
| `RadialEigen.lean` | `robinQ`, `radialH1`, `dirichletBilin_radial`, `qBilin_radial`, `weak_eq_radial`, `qB_radial` | compiles (sonnet, 316 lines) |
| `PiconeBall.lean` | `exists_pos_profile`, `dirichlet_pairing_radial`, `picone_ofC1`, `picone_H1` | compiles (sonnet, 472 lines) |
| `RadialShooting.lean` | `shootSet`, `nuStar`, `nuStar_spec` (`ν* = lam1`, positive radial eigenfunction) | compiles (sonnet, 294 lines) |
| `GroundStateReg.lean` | **`exists_transverseGroundStateReg (n) (hn : 1 ≤ n) (hα : 0 ≤ α) : ∃ R₀ > 0, ∀ R, 0 < R → R < R₀ → ∃ gsr : TransverseGroundStateReg n α R (bdR n R), IsRadialGroundState gsr ∧ IsPositiveGroundState gsr`** | compiles (sonnet, 232 lines), axioms `[propext, Classical.choice, Quot.sound]` |

All 29 files build together (`lake build RobinCaps.Compact.GroundStateReg RobinCaps.Compact.GroundStateExists`,
8374 lines); no `sorry`/`admit`/`axiom`/`native_decide`.  The regular ground state is
`psiReg n R α hn = (NB ψ)^{-1/2} • radialH1 n R (radSeries n (nuStar n R α)) _`, i.e.
`ψ(z) = c · g_{ν*}(‖z‖²)` with `g_ν` the explicit power series `∑ a_k s^k`, `a_{k+1} = −ν a_k/(2(k+1)(2k+n))`,
and `ν* = lam1 α (bdR n R)` obtained by shooting (`RadialShooting.lean`) with Picone's inequality
(`PiconeBall.lean`) supplying minimality.  It is `C^∞`, radial and positive; the gap for small `R`
is inherited from `gap_of_small`.  Entry point: `RobinCaps.Compact.GroundStateReg`.
