import Mathlib

/-!
# RobinCaps.Basic

Shared basic quantities for the Robin end-cap project.

This file is an *interface skeleton* (coordinator `iface-draft-v1`). It contains
definitions that are intended to be shared by all units. Nothing here is a
mathematical result about the paper yet.

Conventions (see `coordinator/SEMANTICS.md`):
* the ambient axial space is `ℝ`, the transverse space is `EuclideanSpace ℝ (Fin m)`;
* `n = m + 1`;
* `volume` is the standard Lebesgue measure normalized as in the manuscript;
* the real model is used throughout.
-/

namespace RobinCaps

/-- Volume `ω_k` of the unit ball in `ℝ^k`. -/
noncomputable def omega (k : ℕ) : ℝ :=
  (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) (1 : ℝ))).toReal

end RobinCaps
