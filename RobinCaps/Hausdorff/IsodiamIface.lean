import RobinCaps.Hausdorff.AreaIface

/-!
# Isodiametric inequality and the Hausdorff normalising constant — interface (wave 13)

Goal: `hConst m = 2^m / ω_m` (`HConstValueProp`), so that `(ω_m / 2^m) • μH[m]` is the standard
(textbook-normalised) `m`-dimensional Hausdorff measure `ℋ^m`. The lower bound is the
isodiametric inequality `|A| ≤ ω_m (diam A / 2)^m` (`IsodiametricProp`), proved by Steiner
symmetrisation in the coordinate directions; the upper bound uses a Vitali covering by balls.

Steiner symmetrisation in coordinate `i` of a set `A ⊆ ℝ^m`: the fibre of `A` through `x` in
direction `i` is `fiberE i A x = {t | updE x i t ∈ A}` (`x` with its `i`-th coordinate replaced by
`t`), and `x ∈ steinerSym i A` iff that fibre is nonempty and `2 |x i| ≤ |fibre|`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace RobinCaps.Hausdorff

/-- `x` with its `i`-th coordinate replaced by `t`. -/
def updE {m : ℕ} (x : EuclideanSpace ℝ (Fin m)) (i : Fin m) (t : ℝ) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (Function.update (fun j => x j) i t)

/-- The fibre of `A` through `x` in coordinate direction `i`. -/
def fiberE {m : ℕ} (i : Fin m) (A : Set (EuclideanSpace ℝ (Fin m))) (x : EuclideanSpace ℝ (Fin m)) :
    Set ℝ :=
  {t | updE x i t ∈ A}

/-- **Steiner symmetrisation** of `A` in coordinate direction `i`. -/
def steinerSym {m : ℕ} (i : Fin m) (A : Set (EuclideanSpace ℝ (Fin m))) :
    Set (EuclideanSpace ℝ (Fin m)) :=
  {x | (fiberE i A x).Nonempty ∧ 2 * |x i| ≤ (volume (fiberE i A x)).toReal}

/-- Reflection in the `i`-th coordinate hyperplane. -/
def reflE {m : ℕ} (i : Fin m) (x : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin m) :=
  updE x i (-(x i))

/-- **Isodiametric inequality** (compact sets). -/
def IsodiametricProp (m : ℕ) : Prop :=
  ∀ A : Set (EuclideanSpace ℝ (Fin m)), IsCompact A →
    volume A ≤ volume (closedBall (0 : EuclideanSpace ℝ (Fin m)) (diam A / 2))

def SteinerCompactProp (m : ℕ) : Prop :=
  ∀ (i : Fin m) (A : Set (EuclideanSpace ℝ (Fin m))), IsCompact A → IsCompact (steinerSym i A)

def SteinerVolumeProp (m : ℕ) : Prop :=
  ∀ (i : Fin m) (A : Set (EuclideanSpace ℝ (Fin m))), IsCompact A →
    volume (steinerSym i A) = volume A

def SteinerDiamProp (m : ℕ) : Prop :=
  ∀ (i : Fin m) (A : Set (EuclideanSpace ℝ (Fin m))), IsCompact A →
    diam (steinerSym i A) ≤ diam A

def SteinerSymmProp (m : ℕ) : Prop :=
  ∀ (i : Fin m) (A : Set (EuclideanSpace ℝ (Fin m))), IsCompact A →
    (∀ x ∈ steinerSym i A, reflE i x ∈ steinerSym i A) ∧
    ∀ j : Fin m, j ≠ i → (∀ x ∈ A, reflE j x ∈ A) →
      ∀ x ∈ steinerSym i A, reflE j x ∈ steinerSym i A

/-- **The value of the normalising constant**: `hConst m = 2^m / ω_m`. -/
def HConstValueProp (m : ℕ) : Prop :=
  hConst m = 2 ^ m / volume (ball (0 : EuclideanSpace ℝ (Fin m)) 1)

end RobinCaps.Hausdorff

end
