# `RobinCaps/Compact/` — C¹ (indeed C^∞) regularity of the transverse ground state

Goal: upgrade `hasTransverseGroundState_bdR` to a `TransverseGroundStateReg` (file
`RobinCaps/ThinDomain/Trial.lean`): the ground state `psi` must be globally `ContDiff ℝ 1` with
`psi.grad = classicalGrad psi.toFun` on the ball.  General elliptic regularity is out of reach in
mathlib; instead we construct the ground state **explicitly as a radial power series**.

## Route

Write `ψ(z) = g(‖z‖²)`.  Then `∇ψ(z) = 2 g'(‖z‖²) z` and
`Δψ = 4 ‖z‖² g''(‖z‖²) + 2n g'(‖z‖²)`, so `Δψ + νψ = 0` iff `4 s g'' + 2n g' + ν g = 0` (`s = ‖z‖²`).
The power series `g_ν(s) = ∑ a_k s^k`, `a_0 = 1`, `a_{k+1} = −ν a_k / (2(k+1)(2k+n))`, solves this and
converges on all of `ℝ` (`|a_k| ≤ |ν|^k / (2^k k!)`), so `ψ_ν(z) = g_ν(‖z‖²)` is `C^∞` on `ℝⁿ`
(composition with the smooth `‖z‖²`; **no differentiability of `‖·‖` at `0` is ever needed**).

* **Divergence theorem on the ball for fields `h(z) z`** (from `bdR_ofC1` with `w = 1`):
  `∫_B (n h + ⟪z, ∇h⟫) = R ∫_{∂B} h dσ`.  Because `∇ψ = h z` with `h = 2 g'(‖z‖²)`, every
  integration by parts below only needs this special case.
* **Weak eigen-equation.** For `C¹` `v`: `∫_B ⟪∇ψ, ∇v⟫ = −∫_B v Δψ + ∫_{∂B} v ∂_nψ`
  (divergence theorem for `h z` with `h = 2 g' v`), and `∂_nψ = 2R g'(R²) ψ/ψ…` i.e.
  `∂_nψ(z) = 2 R g'(R²)` on `∂B`.  Robin condition: `2R g'(R²) + α g(R²) = 0`.  Then
  `qBilin α bdR ψ v = ν NBilin ψ v` for `C¹` `v`, hence for all `v ∈ H1` by density
  (`exists_ofC1_h1_close`) and continuity.
* **Picone.** For `ψ > 0` on the closed ball, `C¹` `v`: pointwise
  `‖∇v‖² − ⟪∇(v²/ψ), ∇ψ⟫ = ‖∇v − (v/ψ)∇ψ‖²`; integrating, with the divergence theorem for
  `(v²/ψ)∇ψ = (2 g' v²/ψ) z`:
  `dirichlet v − ν mass v + ∫_{∂B} (v²/ψ) ∂_nψ = ∫ ‖∇v − (v/ψ)∇ψ‖² ≥ 0`.
  If `2R g'(R²) + α g(R²) ≥ 0` (Robin supersolution) this gives `ν mass v ≤ dirichlet v + α bdR v v`
  for `C¹` `v`, hence for all `v ∈ H1` by density.
* **Shooting.** `S := {ν ≥ 0 | g_ν > 0 on [0,R²] ∧ 2R g_ν'(R²) + α g_ν(R²) ≥ 0}` contains `0`
  (`g_0 ≡ 1`) and is bounded above by `lam1 α (bdR n R)` (Picone).  Let `ν* := sup S`.  By continuity
  of `(ν, s) ↦ g_ν(s), g_ν'(s)` (uniform bounds on compact sets): `g_{ν*} ≥ 0` on `[0,R²]` and the
  Robin quantity is `≥ 0`.  Neither can be strict (else `ν* + ε ∈ S`); a zero of `g_{ν*}` on `[0,R²]`
  is impossible by ODE uniqueness at regular points `s > 0` (`ODE_solution_unique`), and a zero at
  `s = 0` contradicts `g(0) = 1`.  Hence `ψ_{ν*} > 0` and satisfies the Robin condition:
  Picone gives `ν* ≤ lam1`, the eigen-equation gives `qB ψ = ν* NB ψ`, so `lam1 ≤ ν*`.
* **Assembly.** `psi := (NB ψ_{ν*})^{-1/2} • ofC1 R ψ_{ν*}`, `nu := lam1`; `gap_of_small` from
  `GroundStateGap.lean` applies verbatim; `psiC1` and `grad_eq` are by construction.

## Files (all under `RobinCaps/Compact/`, namespace `RobinCaps.Compact`)

Wave 1 (independent):
* `RadialSeries.lean` — `radCoeff`, `radSeries`, summability, `HasDerivAt` (twice), continuity, ODE.
* `GradCalc.lean` — `classicalGrad` of sums, products, quotients, constants.
* `RadialFun.lean` — `radialFun g z := g (‖z‖^2)`: `ContDiff`, gradient `2 g'(‖z‖²) z`, "Laplacian".
* `DivergenceBall.lean` — `∫_B (n h + ⟪z, ∇h⟫) = R * sphereIntegral n R h` for `C¹` `h`.
* `PiconePointwise.lean` — the pointwise Picone identity (pure algebra).

Wave 2: `RadialSeriesCont.lean` (continuity in `ν`), `RadialEigen.lean` (weak eigen-equation),
`PiconeBall.lean` (integrated Picone + density), `RadialShooting.lean`, `GroundStateReg.lean`.
