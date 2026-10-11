/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import AlgebraicCurves.Geometry.Picard.UnrigidifiedGroup
import AlgebraicCurves.Geometry.Picard.AlgEquivZeroGroupCut
import AlgebraicCurves.Geometry.Picard.RelSubPic.Group

/-!
# The group comparison between pointed and unrigidified Picard classes

Forgetting rigidification preserves tensor products on actual representatives.
The normalization equivalence is therefore an equivalence of commutative groups.
-/

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard Opposite
open NeronModelInfra

noncomputable section

namespace AlgebraicGeometry.RelPicard.Unrigidified

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

/-- Forgetting the rigidification is a multiplicative equivalence on Picard-zero classes. -/
def forgetZeroMulEquiv (X : (Over (Spec (CommRingCat.of R)))ᵒᵖ) :
    (relSubPicCommGrpPresheaf c ε (algEquivZeroGroupCut c ε)).obj X ≃*
      (zeroCommGrpPresheaf c).obj X where
  toEquiv := (zeroClassesEquiv ε X.unop.hom).symm
  map_mul' := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    apply Subtype.ext
    induction x using Quotient.ind
    induction y using Quotient.ind
    rfl

/-- Normalization is the inverse multiplicative equivalence. -/
def normalizeZeroMulEquiv (X : (Over (Spec (CommRingCat.of R)))ᵒᵖ) :
    (zeroCommGrpPresheaf c).obj X ≃*
      (relSubPicCommGrpPresheaf c ε (algEquivZeroGroupCut c ε)).obj X :=
  (forgetZeroMulEquiv ε X).symm

end AlgebraicGeometry.RelPicard.Unrigidified
