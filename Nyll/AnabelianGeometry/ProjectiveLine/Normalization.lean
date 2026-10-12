/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.ProjectiveLine.CoordinateChange
import Nyll.AnabelianGeometry.ProjectiveLine.CrossRatioSeparation

/-!
# Normalization of three projective points

Three distinct ordered points admit an explicit invertible coordinate change
sending them to zero, infinity, and one. Its affine coordinate is the cross ratio.
-/

namespace AnabelianGeometry.ProjectiveLine

universe u
variable {K : Type u} [Field K]

/-- A finite point in the standard affine chart. -/
def affinePoint (t : K) : Projectivization K (K × K) :=
  Projectivization.mk K (t, 1) (fun h => one_ne_zero (congrArg Prod.snd h))

/-- The point outside the standard affine chart. -/
def infinityPoint : Projectivization K (K × K) :=
  Projectivization.mk K (1, 0) (fun h => one_ne_zero (congrArg Prod.fst h))

/-- The determinant of the normalization matrix. -/
theorem normalization_determinant (a b c : K × K) :
    (a.2 * bracket c b) * (-b.1 * bracket c a) -
      (-a.1 * bracket c b) * (b.2 * bracket c a) =
        bracket a b * bracket c b * bracket c a := by
  unfold bracket
  ring

/-- Normalize a triple of noncollinear homogeneous representatives. -/
noncomputable def normalizeCoordinates (a b c : K × K)
    (hab : bracket a b ≠ 0) (hcb : bracket c b ≠ 0) (hca : bracket c a ≠ 0) :
    Projectivization K (K × K) ≃ Projectivization K (K × K) :=
  projectiveCoordinateChange (a.2 * bracket c b) (-a.1 * bracket c b)
    (b.2 * bracket c a) (-b.1 * bracket c a)
    (by rw [normalization_determinant]; exact mul_ne_zero (mul_ne_zero hab hcb) hca)

/-- The normalization matrix has the two cross-ratio factors as its coordinates. -/
theorem normalization_transform (a b c d : K × K) :
    transform (a.2 * bracket c b) (-a.1 * bracket c b)
      (b.2 * bracket c a) (-b.1 * bracket c a) d =
        (bracket d a * bracket c b, bracket d b * bracket c a) := by
  apply Prod.ext <;> simp only [transform, bracket] <;> ring

/-- On the complement of the second point, normalization is the affine cross ratio. -/
theorem normalizeCoordinates_mk (a b c d : K × K)
    (hab : bracket a b ≠ 0) (hcb : bracket c b ≠ 0) (hca : bracket c a ≠ 0)
    (hd : d ≠ 0) (hdb : bracket d b ≠ 0) :
    normalizeCoordinates a b c hab hcb hca (Projectivization.mk K d hd) =
      affinePoint (homogeneousCrossRatio a b c d) := by
  change Projectivization.mk K
    (transform (a.2 * bracket c b) (-a.1 * bracket c b)
      (b.2 * bracket c a) (-b.1 * bracket c a) d) _ = _
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
  refine ⟨bracket d b * bracket c a, ?_⟩
  rw [normalization_transform]
  apply Prod.ext
  · change (bracket d b * bracket c a) *
        ((bracket d a * bracket c b) / (bracket d b * bracket c a)) = _
    exact mul_div_cancel₀ _ (mul_ne_zero hdb hca)
  · change (bracket d b * bracket c a) * 1 = _
    exact mul_one _

/-- Normalization sends the first point to zero. -/
theorem normalizeCoordinates_first (a b c : K × K)
    (hab : bracket a b ≠ 0) (hcb : bracket c b ≠ 0) (hca : bracket c a ≠ 0)
    (ha : a ≠ 0) :
    normalizeCoordinates a b c hab hcb hca (Projectivization.mk K a ha) =
      affinePoint 0 := by
  rw [normalizeCoordinates_mk a b c a hab hcb hca ha hab]
  have haa : bracket a a = 0 := by unfold bracket; ring
  simp only [homogeneousCrossRatio, haa, zero_mul, zero_div]

/-- Normalization sends the third point to one. -/
theorem normalizeCoordinates_third (a b c : K × K)
    (hab : bracket a b ≠ 0) (hcb : bracket c b ≠ 0) (hca : bracket c a ≠ 0)
    (hc : c ≠ 0) :
    normalizeCoordinates a b c hab hcb hca (Projectivization.mk K c hc) =
      affinePoint 1 := by
  rw [normalizeCoordinates_mk a b c c hab hcb hca hc hcb]
  have hcr : homogeneousCrossRatio a b c c = 1 := by
    unfold homogeneousCrossRatio
    rw [mul_comm (bracket c a), div_self (mul_ne_zero hcb hca)]
  rw [hcr]

/-- Normalization sends the second point to infinity. -/
theorem normalizeCoordinates_second (a b c : K × K)
    (hab : bracket a b ≠ 0) (hcb : bracket c b ≠ 0) (hca : bracket c a ≠ 0)
    (hb : b ≠ 0) :
    normalizeCoordinates a b c hab hcb hca (Projectivization.mk K b hb) =
      infinityPoint := by
  change Projectivization.mk K
    (transform (a.2 * bracket c b) (-a.1 * bracket c b)
      (b.2 * bracket c a) (-b.1 * bracket c a) b) _ = _
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
  refine ⟨bracket b a * bracket c b, ?_⟩
  rw [normalization_transform]
  apply Prod.ext
  · change (bracket b a * bracket c b) * 1 = _
    exact mul_one _
  · change (bracket b a * bracket c b) * 0 = bracket b b * bracket c a
    unfold bracket
    ring

end AnabelianGeometry.ProjectiveLine
